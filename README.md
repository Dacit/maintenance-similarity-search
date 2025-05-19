# Supporting Maintenance of Formal Mathematics with Similarity Search (Supplementary Material)
This is the supplemental material to the paper
  "Supporting Maintenance of Formal Mathematics with Similarity Search".

## Usage
All data for the paper is located in [data](./data) subdirectory.
Figures can be re-generated with an R environment with the following dependencies:
```
dplyr 1.1.4
tidyr 1.3.1
ggplot2 3.5.1
ggpubr 0.6.0
```
- Fig. 1a: [clone_hol.R](./clone_hol.R)
- Fig. 2: [ranks.R](./ranks.R)

To use the tools developed in the paper,
a working Isabelle2025 installation is assumed to be available as `isabelle` command.
All commands are relative to the root directory of this repository.

### Clone detection
- Installation: `isabelle components -u code/clone-detect`
- Usage hints: `isabelle clone_detect -?`
- Detection for HOL from paper: `isabelle clone_detect -t 0.872 HOL`,
  note that code was modified to not return clone classes.
  Proofs of equality / locale instantiations can be found in [data/Clones_HOL.thy](./data/Clones_HOL.thy)
- Detection for AFP from paper
  (requires intensive hardware resources to build and afp-2025 installed):
  ```
  isabelle clone_detect -d '$AFP' -a -v -X slow \
    -x CRYSTALS-Kyber_Security \
    -x CubicalCategories -x Nominal_Myhill_Nerode \
    -x ResiduatedTransitionSystem2 \
    -x Automated_Stateful_Protocol_Verification
  ```

### Relocate
- Installation: `isabelle components -u code/relocate`
- Usage in example theory: Add `Relocate.Relocate` to imports,
  then the command `relocate <thm>` is available.
  See the [Example theory](./code/relocate/Example.thy).
- Moves extracted from history can be found in [data/move_history.md](./data/relocate_history.md)
- Ranking of the evaluation can be found in [data/relocate_eval.json](./data/relocate_eval.json)