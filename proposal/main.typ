#import "template.typ": *

#show: acmart.with(
  format: "acmsmall",
  title: "CS 747: Formal Verification of Unification-based Pointer Analysis Algorithms",
  authors: {
  let uwaterloo = (
      institution: "University of Waterloo",
      streetaddress: "P.O. Box 1212",
      city: "Waterloo",
      state: "ON",
      country: "Canada",
      postcode: "43017-6221")
  (
    (
      name: "Kevin Lee",
      email: "k323lee@uwaterloo.ca",
      affiliation: uwaterloo),
  )},
  shortauthors: "Lee",
  abstract: [
    // Probably don't need an abstract?
  ],
  ccs: none,
  keywords: none,
)

= Introduction
Pointer analysis or alias analysis is an essential step in static analysis, allowing.

= Template Overview
As noted in the introduction, the "`acmart`" document class can
be used to prepare many different kinds of documentation --- a
double-blind initial submission of a full-length technical paper, a
two-page SIGGRAPH Emerging Technologies abstract, a "camera-ready"
journal article, a SIGCHI Extended Abstract, and more --- all by
selecting the appropriate _template style_ and _template parameters_.

This document will explain the major features of the document
class. For further information, the _Typst User's Guide_ is
available from https://www.acm.org/publications/proceedings-template.

== Template Styles

The primary parameter given to the "`acmart`" document class is
the _template style_ which corresponds to the kind of publication
or SIG publishing the work. This parameter is enclosed in square
brackets and is a part of the `documentclass` command:
```
  \documentclass[STYLE]{acmart}
```

$ 5 / 12 + interrobang $

Journals use one of three template styles. All but three ACM journals
use the `acmsmall` template style:
- `acmsmall`: The default journal template style.
- `acmlarge`: Used by JOCCH and TAP.
- `acmtog`: Used by TOG.

The majority of conference proceedings documentation will use the `acmconf` template style.
- `acmconf`: The default proceedings template style.
- `sigchi`: Used for SIGCHI conference articles.
- `sigplan`: Used for SIGPLAN conference articles.

== Template Parameters

In addition to specifying the _template style_ to be used in
formatting your work, there are a number of _template parameters_
which modify some part of the applied template style. A complete list
of these parameters can be found in the _Typst User's Guide._

Frequently-used parameters, or combinations of parameters, include:
- `anonymous,review`: Suitable for a "double-blind"
  conference submission. Anonymizes the work and includes line
  numbers. Use with the command to print the
  submission's unique ID on each page of the work.
- `authorversion`: Produces a version of the work suitable
  for posting by the author.
- `screen`: Produces colored hyperlinks.

This document uses the following string as the first command in the
source file:
```
\documentclass[acmsmall]{acmart}
```

= Modifications

Modifying the template --- including but not limited to: adjusting
margins, typeface sizes, line spacing, paragraph and list definitions,
and the use of the `\vspace` command to manually adjust the
vertical spacing between elements of your work --- is not allowed.

*Your document will be returned to you for revision if modifications are discovered.*