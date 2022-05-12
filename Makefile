OUT := _out

.PHONY: all
all: $(OUT)/ci.pdf $(OUT)/html/ci.html

%.pdf: %.tex
	cd "$(dir $^)"; latexmk -xelatex "$(notdir $^)"

$(OUT)/html/%.html: %.lagda.tex
	agda --html --html-dir="$(OUT)/html" "$^"

$(OUT)/%.tex: %.lagda.tex
	agda --latex --latex-dir="$(OUT)" "$^"


.PHONY: clean
clean:
	rm -rf "$(OUT)"

