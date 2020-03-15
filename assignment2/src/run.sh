noweave -x -delay 2015PH10813.nw > output.tex
notangle -RbintreeSignature-complete 2015PH10813.nw > bintreeSignature-complete.sml
notangle -RbintreeStructure-complete 2015PH10813.nw > bintreeStructure-complete.sml
notangle -RtestCase-complete 2015PH10813.nw > testCase-complete.sml
pdflatex output.tex