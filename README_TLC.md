TLA+ TLC local setup

This folder contains helper scripts to download and run the TLA+ `tla2tools.jar` (TLC model checker) locally.

Quick install

```bash
# download tla2tools.jar into tools/
bash scripts/install_tla2tools.sh

# run TLC on the sample module (from repo root)
bash scripts/run_tlc.sh SimpleCounter
```

Notes
- The installer downloads a specific release of tla2tools.jar. Update `scripts/install_tla2tools.sh` if you want a different version.
- The wrapper `run_tlc.sh` runs TLC via `java -cp` with `-deadlock` and `-config` options; add flags as needed.

Creating your dataset
- Build small TLA modules in `samples/` or `data/` using the module template in `tla_templates/`.
- `scripts/generate_tla.py` can be used to produce TLA files from NL examples (see its docstring and README).

