OUT := _out

.PHONY: all
all: $(OUT)/ci.pdf

%.pdf: %.tex
	cd "$(dir $^)"; latexmk -xelatex "$(notdir $^)"


$(OUT)/%.tex: %.lagda.tex
	agda --latex --latex-dir="$(OUT)" "$^"


.PHONY: clean
clean:
	rm -rf "$(OUT)"

