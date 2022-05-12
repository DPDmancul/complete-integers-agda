OUT := _out
HTML := $(OUT)/html

MAIN := ci

LITS := $(wildcard *.lagda.tex)

.PHONY: all pdf html
all: pdf html

pdf: $(OUT)/$(MAIN).pdf
html: $(HTML)/$(MAIN).html

$(OUT)/$(MAIN).pdf: $(LITS:%.lagda.tex=$(OUT)/%.tex)
	cd "$(OUT)"; latexmk -xelatex "$(MAIN).tex"

$(HTML)/%.html: %.lagda.tex
	agda --html --html-dir="$(HTML)" "$<"

$(OUT)/%.tex: %.lagda.tex
	agda --latex --latex-dir="$(OUT)" "$<"

.PHONY: clean
clean:
	rm -rf "$(OUT)"

