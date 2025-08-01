% Generated by roxygen2: do not edit by hand
% Please edit documentation in R/arakno.R
\name{authors}
\alias{authors}
\title{Get species authors from WSC.}
\usage{
authors(tax, order = FALSE)
}
\arguments{
\item{tax}{A taxon name or vector with taxa names.}

\item{order}{Order taxa alphabetically or keep as in tax.}
}
\value{
A data.frame with species and authority names.
}
\description{
Get species authority from the World Spider Catalogue.
}
\details{
This function will get species authorities from the World Spider Catalogue (2025). Higher taxa will be converted to species names.
}
\examples{
\dontrun{
authors("Amphiledorus")
authors(tax = c("Iberesia machadoi", "Nemesia bacelarae", "Amphiledorus ungoliantae"), order = TRUE)
}
}
\references{
World Spider Catalog (2025). World Spider Catalog. Version 26. Natural History Museum Bern, online at http://wsc.nmbe.ch. doi: 10.24436/2.
}
