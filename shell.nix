{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
  nativeBuildInputs = with pkgs; [
    gnumake
    gnused
    (agda.withPackages (p: [ p.standard-library ]))
    (texlive.combine { inherit (texlive)
      scheme-small
      xifthen
      ifmtarg
      polytable
      lazylist
      environ
      newunicodechar
      latexmk;
    })
  ];
}
