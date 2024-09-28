with import <nixpkgs> { };
with pkgs.python3Packages;
let pythonEnv = python311.withPackages (ps: [
    ps.toolz
    ps.numpy

    ps.requests
    ps.psutil

    ps.z3
  ]);
in
{ pkgs ? import <nixpkgs> {} }:
  pkgs.mkShell {
    # nativeBuildInputs is usually what you want -- tools you need to run
    nativeBuildInputs = with pkgs.buildPackages; [
      opam
      gmp
      pkg-config
      gtk3
      gtksourceview
      gtk2
      gnome2.gtksourceview
      cairo
      gnome.adwaita-icon-theme

      gnumake42
      parallel
      sqlite

      pythonEnv
    ];
}
