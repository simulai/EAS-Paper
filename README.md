# EAS: Epistemic Axiomatic System

A single-axiom foundation for cognition and intelligence, with mechanized verification in Lean 4.

## Paper

The full paper is in [`EAS-Single-Axiom-Foundation.md`](EAS-Single-Axiom-Foundation.md).

## Lean 4 Formalization

The formal verification of the Two-Stream Decomposition Impossibility theorem is in [`T5_TwoStream_Impossibility.lean`](T5_TwoStream_Impossibility.lean).

### Build

```bash
# Install elan (Lean version manager)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y

# Compile the formalization
lean T5_TwoStream_Impossibility.lean
```

### CI Status

![Lean4 Build](https://github.com/simulai/EAS-Paper/actions/workflows/lean4-build.yml/badge.svg)

## Author

**Jing Zhang** — Independent Researcher

## License

MIT
