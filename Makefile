R := Rscript -e
bookdown = $(R) "bookdown::render_book('_bookdown.yml', 'bookdown::$(1)')"

SRC := $(CURDIR)/src
MAIN := $(SRC)/ci.lagda.md
OUT := $(CURDIR)/_book

.PHONY: all test pdf html
# pdf must be before html in order to create pdf download button
all: pdf html

test:
	cd "$(SRC)"; agda "$(MAIN)"

pdf:
	$(call bookdown,pdf_book)

html: TMP := "$(shell mktemp -d)"
html: TMP_OUT := "$(TMP)/$(notdir $(OUT))"
html:
	@mkdir -p "$(TMP)/$(notdir $(SRC))"
	@mkdir -p "$(TMP_OUT)"
# generate md and html files with agda syntax highlighting
	cd "$(SRC)"; agda --html --html-highlight=auto --html-dir="$(TMP)" "$(MAIN)"
# rename to original names (required by bookdown)
	@cd "$(TMP)"; for e in *.md; do mv "$$e" "$(notdir $(SRC))/$${e%.md}.lagda.md"; done
# copy required configuration files
	@cp *.{yml,Rmd} "$(TMP)/"
	@cp "$(OUT)/"*.pdf "$(TMP_OUT)"
# execute bookdown
	cd "$(TMP)"; $(call bookdown,gitbook)
	@cp -r "$(TMP_OUT)" "$(dir $(OUT))/"
# agda css must have precedence
	@chmod +w "$(TMP)/"*.css
	@sed -i 's/\(;\? *}\|;\)/ !important\1/' "$(TMP)/"*.css
	@cp "$(TMP)/"*.{html,css} "$(OUT)/"
	@rm -rf "$(TMP)"

.PHONY: clean
clean:
	rm -rf "$(OUT)" _minted* *.pyg *.log

