import Lake
open Lake DSL

package «eas-lean4» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩
  ]
  -- add any additional package configuration options here

@[default_target]
lean_lib «EasLean4» where
  -- add any library configuration options here
