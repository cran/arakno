% Generated by roxygen2: do not edit by hand
% Please edit documentation in R/arakno.R
\name{species}
\alias{species}
\title{Get species from higher taxa.}
\usage{
species(tax, order = FALSE)
}
\arguments{
\item{tax}{A taxon name or vector with taxa names.}

\item{order}{Order species names alphabetically.}
}
\value{
A vector with species names.
}
\description{
Get species within given families or genera from the World Spider Catalogue.
}
\details{
This function will get all species currently listed for given families or genera from the World Spider Catalogue (2025).
}
\examples{
\dontrun{
species("Amphiledorus")
species(tax = c("Amphiledorus", "Nemesiidae"), order = TRUE)
}
}
\references{
World Spider Catalog (2025). World Spider Catalog. Version 26. Natural History Museum Bern, online at http://wsc.nmbe.ch. doi: 10.24436/2.
}
