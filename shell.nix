{ pkgs ? import <nixpkgs> { } }:
with pkgs;
mkShell {
  buildInputs = [
    (agda.withPackages [ 
      (agdaPackages.standard-library.overrideAttrs (oldAttrs: {
        version = "2.0";
        src = fetchFromGitHub {
          repo = "agda-stdlib";
          owner = "agda";
          rev = "v2.0";
          hash = "sha256-TjGvY3eqpF+DDwatT7A78flyPcTkcLHQ1xcg+MKgCoE=";
        };
      }))
      (agdaPackages.agda-categories.overrideAttrs (oldAttrs : {
        version = "0.2.0";
         src = fetchFromGitHub {
           repo = "agda-categories";
           owner = "agda";
           rev = "944a487b92ab3a9d3b3ee54d209cd7ea95dc58ed";
           hash = "sha256-G5QgEMj6U+5s3o7HUfORn+Y3gQA9KvpUuAvHAXn7TKk=";
         };

        # without this nix might use a wrong version of the stdlib to try and typecheck agda-categories
        buildInputs = [
          (agda.withPackages [
            (agdaPackages.standard-library.overrideAttrs (oldAttrs: {
              version = "2.0";
              src = fetchFromGitHub {
                repo = "agda-stdlib";
                owner = "agda";
                rev = "v2.0";
                hash = "sha256-TjGvY3eqpF+DDwatT7A78flyPcTkcLHQ1xcg+MKgCoE=";
              };
            }))
          ])
         ];

        GHCRTS = "-M6G";
      }))
    ])
  ];

  shellHook = ''
    # ...
  '';
}
