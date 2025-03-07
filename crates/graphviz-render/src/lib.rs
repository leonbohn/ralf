use thiserror::Error;

pub struct GraphvizSource(String);

pub struct Svg(String);

pub struct PngImage(Vec<u8>);

#[derive(Error, Debug)]
pub enum RenderError {
    #[error("encountered SVG rendering error: \"{0:?}\"")]
    // we let `thiserror` implement From<resvg::usvg::Error>
    SvgError(#[from] resvg::usvg::Error),
    #[error("could not allocate pixmap")]
    PixmapAllocationError,
    #[error("could not encode PNG: \"{0:?}\"")]
    PngEncodingError(String),
    #[error("error when displaying PNG: \"{0:?}\"")]
    PngDisplayError(#[from] std::io::Error),
    #[error("could not render to SVG: \"{0}\"")]
    RenderToSvgError(String),
    #[error("Could not create VSVG document: \"{0}\"")]
    VsvgDocumentError(String),
    #[error("Child process had non-zero exit status \"{0}\"")]
    NonZeroExit(std::process::ExitStatus),
}

/// Attempts to render the object to a file with the given filename. This method
/// is only available on the `graphviz` crate feature and makes use of temporary files.
#[cfg(feature = "graphviz")]
fn render_to_file_name(&self, filename: &str) -> Result<(), std::io::Error> {
    use std::io::{Read, Write};
    use tracing::trace;

    trace!("Outputting dot and rendering to png");
    let dot = self.dot_representation();
    let mut tempfile = tempfile::NamedTempFile::new()?;

    tempfile.write_all(dot.as_bytes())?;
    let tempfile_name = tempfile.path();

    let mut child = std::process::Command::new("dot")
        .arg("-Tpng")
        .arg("-o")
        .arg(filename)
        .arg(tempfile_name)
        .spawn()?;
    if !child.wait()?.success() {
        Err(std::io::Error::new(
            std::io::ErrorKind::Other,
            child
                .stdout
                .map_or("Error in dot...".to_string(), |mut err| {
                    let mut buf = String::new();
                    if let Err(e) = err.read_to_string(&mut buf) {
                        buf = format!("Could not read from stdout: {e}");
                    }
                    buf
                }),
        ))
    } else {
        Ok(())
    }
}

/// First creates a rendered PNG using [`Self::render()`], after which the rendered
/// image is displayed via by using a locally installed image viewer.
/// This method is only available on the `render` crate feature.
///
/// # Image viewer
/// On Macos, the Preview app is used, while on Linux and Windows, the image viewer
/// can be configured by setting the `IMAGE_VIEWER` environment variable. If it is not set,
/// then the display command of ImageMagick will be used.
fn display_rendered_graphviz(&self) -> Result<(), RenderError> {
    display_png(self.render_graphviz()?)?;

    Ok(())
}

/// See [`Self::display_rendered`] but with a native rendering backend.
fn display_rendered(&self) -> Result<(), RenderError> {
    display_png(self.render()?)?;

    Ok(())
}

/// Renders the object visually (as PNG) and returns a vec of bytes/u8s encoding
/// the rendered image. This method is only available on the `graphviz` crate feature
/// and makes use of temporary files.
fn render_graphviz(dot: &GraphvizSource) -> Result<Vec<u8>, RenderError> {
    use std::io::{Read, Write};
    let mut child = std::process::Command::new("dot")
        .arg("-Tpng")
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .spawn()?;

    if let Some(mut stdin) = child.stdin.take() {
        stdin.write_all(dot.0.as_bytes())?;
    }

    let mut output = Vec::new();
    if let Some(mut stdout) = child.stdout.take() {
        stdout.read_to_end(&mut output)?;
    }

    let status = child.wait()?;
    if !status.success() {
        return Err(RenderError::NonZeroExit(status));
    }

    Ok(output)
}

#[cfg(test)]
mod tests {
    use super::*;
}
