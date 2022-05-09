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
#       xcolor
      polytable
      lazylist
#       etoolbox
      environ
#       xkeyval
#       mathtools
      newunicodechar
      latexmk;
    })
  ];
}
