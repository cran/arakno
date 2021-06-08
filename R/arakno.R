#####arakno - ARAchnid KNowledge Online
#####Version 1.1.0 (2021-06-05)
#####By Pedro Cardoso
#####Maintainer: pedro.cardoso@helsinki.fi
#####Reference: None yet.
#####Changed from v1.0.1:
#####Changed name from spidR to arakno
#####Much improved checknames
#####Handling of aff., cf. and subspecies
#####Simplified mapping with no cryptic messages

#####required packages
library("graphics")
library("httr")
library("jsonlite")
library("rgbif")
library("rworldmap")
library("rworldxtra")
library("stats")
library("utils")
#' @import graphics
#' @import httr
#' @import jsonlite
#' @import rgbif
#' @import rworldmap
#' @import rworldxtra
#' @import stats
#' @import utils

globalVariables(c("wscdata", "wscmap"))

################################################################################
################################AUX FUNCTIONS###################################
################################################################################

getTax <- function(tax){

  #if any taxa not found break execution
  if(length(checknames(tax)) > 1){
    warning(paste("Some names were not found in WSC:", checknames(tax)[,1]))
    stop("Please run arakno::checknames() to check and possibly correct")
  }

  newTax = c()
  #convert families and genera to species
  for(t in 1:length(tax)){
    if (sapply(strsplit(tax[t], " "), length) > 1){
      newTax = c(newTax, tax[t])
    } else {
      newTax = c(newTax, species(tax[t]))
    }
  }
  return(unique(newTax))
}

#function adapted from rworldmaps
joinMap <- function (dF, hires){

  joinCode = "ISO3"
  nameJoinColumn = "code"
  nameCountryColumn = "Country"
  suggestForFailedCodes = FALSE
  projection = NA
  mapResolution = ifelse(hires, "high", "coarse")

  mapWithData <- getMap(resolution = mapResolution)
  listJoinCodesNew <- c("ISO_A2", "ISO_A3", "FIPS_10_",
                        "ADMIN", "ISO_N3")
  listJoinCodesOld <- c("ISO2", "ISO3", "FIPS",
                        "NAME", "UN")
  listJoinCodes <- c(listJoinCodesOld, listJoinCodesNew)
  if (joinCode %in% listJoinCodes == FALSE) {
    stop("your joinCode (", joinCode, ") in joinCountryData2Map() is not one of those supported. Options are :",
         paste(listJoinCodes, ""), "\n")
    return(FALSE)
  }
  joinCodeOld <- joinCode
  if (joinCode %in% listJoinCodesOld) {
    joinCode <- listJoinCodesNew[match(joinCode, listJoinCodesOld)]
  }
  dF[[joinCode]] <- as.character(dF[[nameJoinColumn]])
  dF[[joinCode]] <- gsub("[[:space:]]*$", "", dF[[joinCode]])
  if (joinCode == "ADMIN") {
    dF$ISO3 <- NA
    for (i in 1:nrow(dF)) dF$ISO3[i] = rwmGetISO3(dF[[joinCode]][i])
    joinCode = "ISO3"
    nameCountryColumn = nameJoinColumn
  }
  matchPosnsInLookup <- match(as.character(dF[[joinCode]]),
                              as.character(mapWithData@data[[joinCode]]))
  failedCodes <- dF[[joinCode]][is.na(matchPosnsInLookup)]
  numFailedCodes <- length(failedCodes)
  numMatchedCountries <- nrow(dF) - numFailedCodes
  failedCountries <- dF[[nameCountryColumn]][is.na(matchPosnsInLookup)]
  failedCountries <- cbind(failedCodes, failedCountries = as.character(failedCountries))
  matchPosnsInUserData <- match(as.character(mapWithData@data[[joinCode]]),
                                as.character(dF[[joinCode]]))
  codesMissingFromUserData <- as.character(mapWithData@data[[joinCode]][is.na(matchPosnsInUserData)])
  countriesMissingFromUserData <- as.character(mapWithData@data[["NAME"]][is.na(matchPosnsInUserData)])
  numMissingCodes <- length(codesMissingFromUserData)
  mapWithData@data <- cbind(mapWithData@data, dF[matchPosnsInUserData,
  ])
  invisible(mapWithData)
}

################################################################################
################################MAIN FUNCTIONS##################################
################################################################################

#' Downloads WSC data.
#' @description Downloads the most recent data from the World Spider Catalogue.
#' @details The World Spider Catalog (2021) lists all currently valid species of spiders, from Clerck to date. Updated daily.
#' @return A matrix with all current species names and distribution. This should be used for other functions using wsc data.
#' @references World Spider Catalog (2021). World Spider Catalog. Version 22.0. Natural History Museum Bern, online at http://wsc.nmbe.ch. doi: 10.24436/2.
#' @examples \dontrun{
#' wsc()
#' }
#' @export
wsc <- function(){

  if(!exists("wscdata") || is.null(wscdata) || ((Sys.time() - attributes(wscdata)$lastUpdate) > 1440)){

    #fetch data from wsc (try both current and previous day)
    today = gsub("-", "", as.character(Sys.Date()))
    yesterday = gsub("-", "", as.character(Sys.Date()-1))
    wscdata = tryCatch(read.csv2(paste("https://wsc.nmbe.ch/resources/species_export_", today, ".csv", sep = ""), sep = ",", encoding = "UTF-8"),
                       warning = function(x) x = read.csv2(paste("https://wsc.nmbe.ch/resources/species_export_", yesterday, ".csv", sep = ""), sep = ","), encoding = "UTF-8")
    #clean data
    wscdata[,1] = do.call(paste, wscdata[, 4:5])
    colnames(wscdata)[1:2] = c("name", "lsid")
    attr(wscdata, 'lastUpdate') = Sys.time()

    #set wscdata as global variable
    pos <- 1
    envir = as.environment(pos)
    assign("wscdata", wscdata, envir = envir)
  }
}

#' Check taxa names in WSC.
#' @description Check taxa names against the World Spider Catalogue.
#' @param tax A taxon name or vector with taxa names.
#' @param full returns the full list of names.
#' @param order Order taxa alphabetically or keep as in tax.
#' @details This function will check if all species, genera and family names in tax are updated according to the World Spider Catalogue (2021). If not, it returns a matrix with nomenclature changes, valid synonyms or possible misspellings using fuzzy matching (Levenshtein edit distance).
#' @return If any mismatches, a matrix with taxa not found in WSC or, if full = TRUE, the full list of names.
#' @references World Spider Catalog (2021). World Spider Catalog. Version 22.0. Natural History Museum Bern, online at http://wsc.nmbe.ch. doi: 10.24436/2.
#' @examples \dontrun{
#' tax = c("Nemesis", "Nemesia brauni", "Iberesia machadoi", "Nemesia bacelari")
#' checknames(tax)
#' checknames(tax, full = TRUE, order = TRUE)
#' }
#' @export
checknames <- function(tax, full = FALSE, order = FALSE){

  #test if any name is longer than 2 words (e.g., subspecies, cf., aff.)
  if(any(sapply(strsplit(tax, " "), length) > 2))
    stop("Some names are longer than 2 words (e.g., subspecies, cf., aff.) and cannot be checked.\nPlease use only species, genera or family names.")

  wsc()

  #get all species, genera and family names
  allNames = unique(c(wscdata[,1], wscdata[,3], wscdata[,4]))

  mismatches = tax[!(tax %in% allNames)]
  if(length(mismatches) == 0) {
    return("All taxa OK!")
  } else {
    mismatches = cbind(mismatches, matrix(NA, nrow = length(mismatches), ncol = 3))
    colnames(mismatches) = c("Species", "Best match", "Note", "Alternative match(es)")
    for(i in 1:nrow(mismatches)){

      #detect nomenclature changes or synonyms
      tax2 = sub(" ", "%20", mismatches[i, 1])
      id = httr::GET(paste("https://spidertraits.sci.muni.cz/backend/taxonomy/valid-names?taxon=", tax2, sep = ""))
      id = httr::content(id)

      #if no changes or synonyms detect misspellings
      if(is.null(id$item)){
        d = adist(allNames, mismatches[i, 1])
        id = allNames[which(d == min(d))]
        mismatches[i, 3] = "Misspelling"
        if(length(id) == 1){
          mismatches[i, 2] = id
        } else {
          mismatches[i, 2] = id[1]
          mismatches[i, 4] = paste(id[2:length(id)], collapse = ", ")
        }
      } else {
        #create matrix with all possible matches (lsid, epithet)
        matchList = c()
        for(s in 1:(length(id$items)))
          matchList = rbind(matchList, c(id$items[[s]]$lsid, id$items[[s]]$genus, id$items[[s]]$species, NA))

        #Detect nomenclature change by matching the first three letters of
        #correct and wrong specific epithet. Not guaranteed but should be ok 90%.
        origSpecies = substring(mismatches[i, 1], gregexpr(" ", mismatches[i, 1])[[1]] + 1, )
        for(s in 1:nrow(matchList)){
          if(substring(matchList[s, 3], 1, 3) == substring(origSpecies, 1, 3))
            matchList[s, 4] = "Nomenclature change"
          else
            matchList[s, 4] = "Synonym"
        }

        #Order alphabetically the change column so that nomenclature comes first
        matchList = matchList[order(matchList[, 4]), , drop = FALSE]
        mismatches[i, 2:3] = c(paste(matchList[1, 2:3], collapse = " "), matchList[1, 4])
        if(nrow(matchList) == 2)
          mismatches[i, 4] = paste(matchList[2, 2:3], collapse = " ")
        if(nrow(matchList) > 2)
          mismatches[i, 4] = paste(matchList[2:nrow(matchList), 2:3], collapse = ", ")
      }
    }

    if(full){
      fulltable = cbind(tax, tax, rep("Ok", length(tax)), NA)
      colnames(fulltable) = c("Species", "Best match", "Note", "Alternative match(es)")
      fulltable[which(tax %in% mismatches[,1]), 2:4] = mismatches [, 2:4]
      mismatches = fulltable
    }
    if(order)
      mismatches = mismatches[order(mismatches[, 1]), ]
    return(mismatches)
  }
}

#' Get species authors from WSC.
#' @description Get species authority from the World Spider Catalogue.
#' @param tax A taxon name or vector with taxa names.
#' @param order Order taxa alphabetically or keep as in tax.
#' @details This function will get species authorities from the World Spider Catalogue (2021). Higher taxa will be converted to species names.
#' @return A data.frame with species and authority names.
#' @references World Spider Catalog (2021). World Spider Catalog. Version 22.0. Natural History Museum Bern, online at http://wsc.nmbe.ch. doi: 10.24436/2.
#' @examples \dontrun{
#' authors("Amphiledorus")
#' authors(tax = c("Iberesia machadoi", "Nemesia bacelarae", "Amphiledorus ungoliantae"), order = TRUE)
#' }
#' @export
authors <- function(tax, order = FALSE){

  wsc()
  tax = getTax(tax)

  filterTable = wscdata[wscdata$name %in% tax,]
  results = filterTable[,c(1,7)]
  if(order)
    results = results[order(results[, 1]), ]
  else
    results = results[order(match(results[, 1], tax)), ]
  colnames(results) = c("Species", "Authors")
  rownames(results) = NULL
  for(sp in 1:nrow(results)){
    results$Authors[sp] = paste(filterTable$author[sp],", ", filterTable$year[sp], sep = "")
    if(filterTable$parentheses[sp] == 1)
      results$Authors[sp] = paste("(", results$Authors[sp],")", sep = "")
  }
  return(results)
}

#' Get species distributions from WSC.
#' @description Get species distribution from the World Spider Catalogue.
#' @param tax A taxon name or vector with taxa names.
#' @param order Order taxa alphabetically or keep as in tax.
#' @details This function will get species distributions from the World Spider Catalogue (2021).
#' @return A data.frame with species and distribution. Family and genera names will be converted to species.
#' @references World Spider Catalog (2021). World Spider Catalog. Version 22.0. Natural History Museum Bern, online at http://wsc.nmbe.ch. doi: 10.24436/2.
#' @examples \dontrun{
#' distribution("Nemesia")
#' distribution(tax = c("Iberesia machadoi", "Amphiledorus ungoliantae"), order = TRUE)
#' }
#' @export
distribution <- function(tax, order = FALSE){

  wsc()
  tax = getTax(tax)

  results = wscdata[wscdata$name %in% tax, c(1, 10)]
  if(order)
    results = results[order(results[, 1]), ]
  else
    results = results[order(match(results[, 1], tax)), ]
  colnames(results) = c("Species", "Distribution")
  rownames(results) = NULL
  return(results)
}

#' Get species LSID from WSC.
#' @description Get species LSID from the World Spider Catalogue.
#' @param tax A taxon name or vector with taxa names.
#' @param order Order taxa names alphabetically or keep as in tax.
#' @details This function will get species LSID from the World Spider Catalogue (2021). Family and genera names will be converted to species.
#' @return A data.frame with species and LSID.
#' @references World Spider Catalog (2021). World Spider Catalog. Version 22.0. Natural History Museum Bern, online at http://wsc.nmbe.ch. doi: 10.24436/2.
#' @examples \dontrun{
#' lsid("Anapistula")
#' lsid(tax = c("Iberesia machadoi", "Nemesia bacelarae", "Amphiledorus ungoliantae"), order = TRUE)
#' }
#' @export
lsid <- function(tax, order = FALSE){

  wsc()
  tax = getTax(tax)

  results = wscdata[wscdata$name %in% tax, 1:2]
  if(order)
    results = results[order(results[, 1]), ]
  else
    results = results[order(match(results[, 1], tax)), ]
  colnames(results) = c("Species", "LSID")
  rownames(results) = NULL
  return(results)
}

#' Get species from higher taxa.
#' @description Get species within given families or genera from the World Spider Catalogue.
#' @param tax A taxon name or vector with taxa names.
#' @param order Order species names alphabetically.
#' @details This function will get all species currently listed for given families or genera from the World Spider Catalogue (2021).
#' @return A vector with species names.
#' @references World Spider Catalog (2021). World Spider Catalog. Version 22.0. Natural History Museum Bern, online at http://wsc.nmbe.ch. doi: 10.24436/2.
#' @examples \dontrun{
#' species("Amphiledorus")
#' species(tax = c("Amphiledorus", "Nemesiidae"), order = TRUE)
#' }
#' @export
species <- function(tax, order = FALSE){

  wsc()
  allPossible = unique(c(wscdata$family, wscdata$genus))
  if(any(!(tax %in% allPossible)))
    stop("The name(s) ", tax[!(tax %in% allPossible)], " were not found in WSC\n")

  results = c(wscdata[wscdata$family %in% tax, 1], wscdata[wscdata$genus %in% tax, 1])
  results = unique(results)
  if(order)
    results = results[order(results)]

  return(results)
}

#' Get taxonomy from species.
#' @description Get species sub/infraorder, family and genus from the World Spider Catalogue.
#' @param tax A taxon name or vector with taxa names.
#' @param check species names should be replaced by possible matches in the WSC if outdated.
#' @param aut add species authorities.
#' @param id the lsid should be returned.
#' @param order Order taxa names alphabetically or keep as in tax.
#' @details This function will get species sub/infraorder, family and genus from the World Spider Catalogue (2021). Optionally, it will correct the species names (using function checknames) and provide the lsid and authors from the WSC (using functions lsid and authors).
#' @return A data.frame with species and taxonomy.
#' @references World Spider Catalog (2021). World Spider Catalog. Version 22.0. Natural History Museum Bern, online at http://wsc.nmbe.ch. doi: 10.24436/2.
#' @examples \dontrun{
#' taxonomy("Symphytognathidae", order = TRUE, aut = TRUE)
#' taxonomy(c("Nemesia machadoi", "Nemesia bacelari"), check = TRUE, aut = TRUE, id = TRUE)
#' }
#' @export
taxonomy <- function(tax, check = FALSE, aut = FALSE, id = FALSE, order = FALSE){

  wsc()
  if(check)
    tax = checknames(tax, full = TRUE)[, 2]
  tax = getTax(tax)

  results = wscdata[wscdata$name %in% tax, c(2,3,4,1)]
  for(i in 1:nrow(results)){
    if(results$family[i] == "Liphistiidae")
      results$lsid[i] = "Mesothelae"
    else if (results$family[i] %in% c("Antrodiaetidae", "Atypidae", "Hexureliidae", "Mecicobothriidae", "Megahexuridae", "Actinopodidae", "Anamidae", "Atracidae", "Barychelidae", "Bemmeridae", "Ctenizidae", "Cyrtaucheniidae", "Dipluridae", "Entypesidae", "Euagridae", "Euctenizidae", "Halonoproctidae", "Hexathelidae", "Idiopidae", "Ischnothelidae", "Macrothelidae", "Microhexuridae", "Microstigmatidae", "Migidae", "Nemesiidae", "Paratropididae", "Porrhothelidae", "Pycnothelidae", "Stasimopidae", "Theraphosidae"))
      results$lsid[i] = "Mygalomorphae"
    else
      results$lsid[i] = "Araneomorphae"
  }
  colnames(results)[1:4] = c("Sub/Infraorder", "Family", "Genus", "Species")
  rownames(results) = NULL

  if(order)
    results = results[order(results[, 1], results[, 2], results[, 3], results[, 4]), ]
  else
    results = results[order(match(results[, 4], tax)), ]

  if(aut)
    results$Authors = authors(results$Species)$Authors

  if(id)
    results$LSID = lsid(results$Species)$LSID

  return(results)
}

#' Get trait data from WST.
#' @description Downloads the most recent data from the World Spider Trait database.
#' @param tax A taxon name or vector with taxa names.
#' @param trait A vector with required trait(s) as abbreviations. Valid values can be found at: https://spidertraits.sci.muni.cz/traits
#' @param sex A vector with required sex(es).
#' @param life A vector with required life stage(s).
#' @param country A vector with required country(ies) ISO3 code(s).
#' @param habitat A vector with required habitat(s).
#' @param user To obtain restricted data get a user name from https://spidertraits.sci.muni.cz/api.
#' @param key To obtain restricted data get an api key from https://spidertraits.sci.muni.cz/api.
#' @param order Order taxa names alphabetically or keep as in tax.
#' @param verbose Display information as data are retrieved.
#' @details The World Spider Trait database (Pekar et al. 2021) has been designed to contain trait data in a broad sense, from morphological traits to ecological characteristics, ecophysiology, behavioural habits, and more (Lowe et al. 2020). This function will download everything available for the taxa given, possibly filtered to the traits given in parameter trait. Some data might be restricted access, in which case a user name and api key are needed (https://spidertraits.sci.muni.cz/api), otherwise the value will show as NA.
#' @return A matrix with trait data.
#' @references Lowe, E., Wolff, J.O., Aceves-Aparicio, A., Birkhofer, K., Branco, V.V., Cardoso, P., Chichorro, F., Fukushima, C.S., Goncalves-Souza, T., Haddad, C.R., Isaia, M., Krehenwinkel, H., Audisio, T.L., Macias-Hernandez, N., Malumbres-Olarte, J., Mammola, S., McLean, D.J., Michalko, R., Nentwig, W., Pekar, S., Petillon, J., Privet, K., Scott, C., Uhl, G., Urbano-Tenorio, F., Wong, B.H. & Herbestein, M.E. (2020). Towards establishment of a centralized spider traits database. Journal of Arachnology, 48: 103-109. https://doi.org/10.1636/0161-8202-48.2.103
#' @references Pekar, S., Cernecka, L., Wolff, J., Mammola, S., Cardoso, P., Lowe, E., Fukushima, C.S., Birkhofer, K. & Herberstein, M.E. (2021). The world spider trait database. Masaryk University, Brno, URL: https://spidertraits.sci.muni.cz
#' @examples \dontrun{
#' traits("Atypus affinis")
#' traits("Atypus", order = TRUE)
#' traits("Atypidae", country = c("PRT", "CZE"), order = TRUE)
#' traits(c("Zodarion costapratae", "Zodarion alacre"))
#' traits(c("Iberesia machadoi", "Zodarion costapratae"), trait = c("balo", "bole"))
#' }
#' @export
traits <- function(tax, trait = NULL, sex = NULL, life = NULL, country = NULL, habitat = NULL, user = "", key = "", order = FALSE, verbose = TRUE){

  wsc()

  #in wst information can also be at family or genus level
  higher = c()
  for(t in tax){
    if(t %in% wscdata$family || t %in% wscdata$genus)
      higher = c(higher, t)
  }
  tax = getTax(tax)
  tax = c(higher, tax)

  results = c()
  for(t in tax){
    if(verbose)
      message("Retrieving data for ", t, "\n")
    if(t %in% wscdata$family) {            #if family
      newTraits = httr::GET(paste("https://spidertraits.sci.muni.cz/backend/data/family/", t, "/genus/*/species/*/original-name/*/trait-category/*/trait/*/method/*/location/*/country/*/dataset/*/authors/*/reference/*/row-link/*?offset=0&limit=10000", sep = ""), authenticate(user, key, "basic"))
    } else if(t %in% wscdata$genus) {           #if genus
      newTraits = httr::GET(paste("https://spidertraits.sci.muni.cz/backend/data/family/*/genus/", t, "/species/*/original-name/*/trait-category/*/trait/*/method/*/location/*/country/*/dataset/*/authors/*/reference/*/row-link/*?offset=0&limit=10000", sep = ""), authenticate(user, key, "basic"))
    } else {                                #if species
      t = sub(" ", "+", t)
      id = httr::GET(paste("https://spidertraits.sci.muni.cz/backend/taxonomy?offset=0&limit=10&searchField=fullName&searchValue=", t, "&count=true", sep = ""))
      id = content(id)$items[[1]]$id
      newTraits = httr::GET(paste("https://spidertraits.sci.muni.cz/backend/data/family/*/genus/*/species/", id, "/original-name/*/trait-category/*/trait/*/method/*/location/*/country/*/dataset/*/authors/*/reference/*/row-link/*?offset=0&limit=10000", sep = ""), authenticate(user, key, "basic"))
    }
    newTraits = as.data.frame(jsonlite::fromJSON(content(newTraits, "text"), flatten = TRUE)$items)

    #apply filters
    if(nrow(newTraits) > 0){
      if(!is.null(trait))
        newTraits = newTraits[newTraits$trait.abbrev %in% trait, ]
      if(!is.null(sex))
        newTraits = newTraits[newTraits$sex.name %in% sex, ]
      if(!is.null(life))
        newTraits = newTraits[newTraits$lifeStage.name %in% life, ]
      if(!is.null(country))
        newTraits = newTraits[newTraits$country.code %in% country, ]
      if(!is.null(habitat))
        newTraits = newTraits[newTraits$habitat %in% habitat, ]
      if(colnames(newTraits)[38] == "location.coords"){
        colnames(newTraits)[38] = "location.coords.lat"
        newTraits$location.coords.lon = newTraits$location.coords.lat
        newTraits = newTraits[,c(1:38, 48, 39:47)]
      }
    }
    results = rbind(results, newTraits)
  }
  if(length(results) == 0)
    return("No results found!")
  colnames(results) = gsub("items.", "", colnames(results))
  if(order)
    results = results[order(results[, 2]), ]
  results = unique(results)
  return(results)
}

#' Get coordinate data from GBIF and WST.
#' @description Downloads coordinate data from records in GBIF and the World Spider Trait database.
#' @param tax A taxon name or vector with taxa names.
#' @param order Order taxa names alphabetically or keep as in tax.
#' @param verbose Display information as data are retrieved.
#' @details Outputs non-duplicate records with geographical (long, lat) coordinates.
#' As always when using data from multiple sources the user should be careful and check if records "make sense" before using them.
#' @return A data.frame with species name, longitude, latitude, source database and reference.
#' @references Pekar, S., Cernecka, L., Wolff, J., Mammola, S., Cardoso, P., Lowe, E., Fukushima, C.S., Birkhofer, K. & Herberstein, M.E. (2021). The world spider trait database. Masaryk University, Brno, URL: https://spidertraits.sci.muni.cz
#' @examples \dontrun{
#' records("Pardosa hyperborea")
#' records(tax = c("Pardosa hyperborea", "Anapistula"), order = TRUE)
#' }
#' @export
records <- function(tax, order = FALSE, verbose = TRUE){

  wsc()
  tax = getTax(tax)

  results = c()
  for (sp in tax){

    #get GBIF data
    gdata = occ_data(scientificName = sp)$data
    if(length(gdata) > 1 && "decimalLongitude" %in% colnames(gdata)){
      gdoi = c()
      for(g in 1:nrow(gdata))
        gdoi[g] = content(httr::GET(paste("https://api.gbif.org/v1/dataset/", gdata$datasetKey[g], sep = ""), limit = 10000))$doi
      gdata = data.frame(long = gdata$decimalLongitude, lat = gdata$decimalLatitude, database = ("GBIF"), reference = gdoi)
      gdata = data.frame(species = rep(sp, nrow(gdata)), gdata)
      results = rbind(results, gdata)
    }

    #get WST data
    tdata = traits(sp, verbose = verbose)
    if(length(tdata) > 1){
      tdata = data.frame(long = tdata$location.coords.lon, lat = tdata$location.coords.lat, database = ("WST"), reference = tdata$reference.abbrev)
      tdata = data.frame(species = rep(sp, nrow(tdata)), tdata)
      results = rbind(results, tdata)
    }
  }

  #remove NA and duplicate values
  results = results[complete.cases(results), ]
  results = unique(results)
  if(order)
    results = results[order(results[, 1]), ]
  rownames(results) = NULL

  return(results)

}

#' Map species ranges.
#' @description Maps species range according to the World Spider Catalogue and records according to GBIF and the World Spider Trait database.
#' @param tax A taxon name or vector with taxa names.
#' @param countries Maps countries according to WSC.
#' @param records Maps records according to GBIF and WST.
#' @param hires Provides high resolution maps. Beware it might take longer to render.
#' @param zoom If records is TRUE, the map will be zoomed to the region with records.
#' @param order Order taxa names alphabetically or keep as in tax.
#' @param verbose Display information as data are retrieved.
#' @details Countries based on the interpretation of the textual descriptions available at the World Spider Catalogue (2021). These might be only approximations to country level and should be taken with caution.
#' @return A world map with countries and records highlighted.
#' @references Pekar, S., Cernecka, L., Wolff, J., Mammola, S., Cardoso, P., Lowe, E., Fukushima, C.S., Birkhofer, K. & Herberstein, M.E. (2021). The world spider trait database. Masaryk University, Brno, URL: https://spidertraits.sci.muni.cz
#' @references World Spider Catalog (2021). World Spider Catalog. Version 22.0. Natural History Museum Bern, online at http://wsc.nmbe.ch. doi: 10.24436/2.
#' @examples \dontrun{
#' map(c("Pardosa hyperborea"))
#' map("Amphiledorus", zoom = TRUE, hires = TRUE)
#' map(c("Pardosa hyperborea", "Iberesia machadoi"), countries  = FALSE, hires = TRUE, zoom = TRUE)
#' }
#' @export
map <- function(tax, countries = TRUE, records = TRUE, hires = FALSE, zoom = FALSE, order = FALSE, verbose = TRUE){

  wsc()
  data(wscmap, package = "arakno", envir = environment())

  #preprocess data
  tax = getTax(tax)
  if(order)
    tax = tax[order(tax)]

  oldpar <- par(no.readonly = TRUE)
  on.exit(par(oldpar))

  #allow plotting multiple taxa
  if(length(tax) == 1)
    par(mfrow = c(1,1))
  else if(length(tax) == 2)
    par(mfrow = c(1,2))
  else if(length(tax) > 16)
    stop("Too many maps to display simultaneously")
  else
    par(mfrow = c(ceiling(length(tax)^0.5),ceiling(length(tax)^0.5)))

  for(sp in tax){
    if(countries){
      #get distribution
      distribution = wscdata[wscdata$name == sp, 10]
      distribution = tolower(strsplit(distribution, c("\\, | and | to |from |\\?|\\/|probably|possibly|introduced"))[[1]]) #split text in chunks
      distribution = sub("\\(.*", "", distribution) #remove everything after parentheses
      distribution = gsub("^\\s+|\\s+$", "", distribution) #remove trailing and white spaces

      #convert distribution to ISO codes
      iso = wscmap[wscmap[,1] %in% distribution, -1]
      iso = colSums(iso)
      iso = names(iso[iso > 0])

      #merge iso codes with map
      iso = unique(iso)
    } else {
      iso = c("STP")
    }
    iso = data.frame(code = iso, exists = rep(1, length(iso)))
    countryRegions <- joinMap(iso, hires) #calls adapted function

    #plot map
    if(!zoom)
      mapCountryData(countryRegions, nameColumnToPlot = "exists", mapTitle = sp, catMethod = "categorical", addLegend = FALSE, colourPalette = "negpos8", oceanCol = "lightblue", missingCountryCol = "white")
    if(records)
      rec = records(sp, verbose = verbose)[2:3]
    if(zoom && records) {
      xlim = c((min(rec[,1]) - 2), (max(rec[,1]) + 2))
      ylim = c((min(rec[,2]) - 2), (max(rec[,2]) + 2))
      mapCountryData(countryRegions, nameColumnToPlot = "exists", mapTitle = sp, catMethod = "categorical", addLegend = FALSE, colourPalette = "negpos8", oceanCol = "lightblue", missingCountryCol = "white", xlim = xlim, ylim = ylim)
    }
    if(records)
      points(rec, pch = 21, col = "black", bg = "white")
  }
}

#' Matrix matching WSC and ISO3 country codes.
#'
#' A dataset that links species distribution descriptions with the map using the ISO3 code
#'
#' @docType data
#' @keywords datasets
#' @name wscmap
#' @usage data(wscmap)
#' @format A matrix with regions and corresponding ISO3 codes.
NULL
