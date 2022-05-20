R := Rscript -e
bookdown = $(R) "bookdown::render_book('_bookdown.yml', 'bookdown::$(1)')"

SRC := $(CURDIR)/src
MAIN := $(SRC)/ci.lagda.md
OUT := $(CURDIR)/_book

.PHONY: all test pdf html
all: pdf html

test:
	cd "$(SRC)"; agda "$(MAIN)"

pdf:
	$(call bookdown,pdf_book)

html: TMP := $(shell mktemp -d)
html:
	@mkdir -p "$(TMP)/$(notdir $(SRC))"
	cd "$(SRC)"; agda --html --html-highlight=auto --html-dir="$(TMP)" "$(MAIN)"
	@cd "$(TMP)"; for e in *.md; do mv "$$e" "$(notdir $(SRC))/$${e%.md}.lagda.md"; done
	@cp *.{yml,Rmd} "$(TMP)/"
	cd "$(TMP)"; $(call bookdown,gitbook)
	@cp -r "$(TMP)/$(notdir $(OUT))" "$(dir $(OUT))/"
	@chmod +w "$(TMP)/"*.css
	@sed -i 's/\(;\? *}\|;\)/ !important\1/' "$(TMP)/"*.css
	@cp "$(TMP)/"*.{html,css} "$(OUT)/"
	@rm -rf "$(TMP)"

.PHONY: clean
clean:
	rm -rf "$(OUT)" _minted* *.pyg *.log

