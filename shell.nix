{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
  nativeBuildInputs = with pkgs; [
    gnumake
    gnused
    which
    pandoc
    (agda.withPackages (p: [
      p.standard-library  # version 1.7.1
    ]))
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
