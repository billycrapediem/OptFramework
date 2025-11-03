import Lake
open Lake DSL

package OptFramework where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]

@[default_target]
lean_lib OptFramework where


require optlib from git
  "https://github.com/optsuite/optlib" @ "main"
