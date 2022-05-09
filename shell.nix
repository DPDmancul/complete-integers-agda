{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
  nativeBuildInputs = with pkgs; [
    gnumake
    gnused
    agda
    pandoc
    (texlive.combine { inherit (texlive)
      scheme-basic
      xcolor
      booktabs
      etoolbox
      mdwtools;
    })
    ( rWrapper.override{ packages = with rPackages; [
      bookdown
    ]; })
  ];
}
