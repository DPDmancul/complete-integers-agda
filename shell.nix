{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
  nativeBuildInputs = with pkgs; [
    gnumake
    gnused
    pandoc
    (agda.withPackages (p: [ p.standard-library ]))
    pythonPackages.pygments
    (texlive.combine { inherit (texlive)
      scheme-basic
      newunicodechar
      xcolor
      booktabs
      etoolbox
      mdwtools
      fancyvrb
      framed
      fvextra
      upquote
      lineno
      catchfile
      xstring
      float
      minted;
    })
    ( rWrapper.override{ packages = with rPackages; [
      bookdown
    ]; })
  ];
}
