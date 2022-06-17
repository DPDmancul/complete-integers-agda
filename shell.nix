{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
  nativeBuildInputs = with pkgs; [
    gnumake
    gnused
    which
    pandoc
    (agda.withPackages (p: [
      (p.standard-library.overrideAttrs (oldAttrs: rec {
        version = "1.7.1";
        src = fetchFromGitHub {
          repo = "agda-stdlib";
          owner = "agda";
          rev = "v${version}";
          sha256 = "0khl12jvknsvjsq3l5cbp2b5qlw983qbymi1dcgfz9z0b92si3r0";
        };
      }))
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
