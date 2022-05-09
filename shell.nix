{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
  nativeBuildInputs = with pkgs; [
    gnumake
    gnused
    agda
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
