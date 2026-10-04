#!/usr/bin/env python3
"""Fill the `formal_proof` link and the [Kit26] reference link in
`FClikeLean/QuantumExtremalNumber.lean`, and the Lean4Web link of `README.md`.

Run from the repository root after pushing:

    python3 lean/scripts/fill_links.py KitaKen1/<repo> <full-commit-sha>

The `formal_proof` link points at the line of `qex_nine` in `lean/Qex94/Main.lean`.
"""
import pathlib
import sys

repo, sha = sys.argv[1], sys.argv[2]
root = pathlib.Path(__file__).resolve().parents[2]
fc = root / "FClikeLean" / "QuantumExtremalNumber.lean"
targets = {
    "QEX_NINE": ("lean/Qex94/Main.lean", "theorem qex_nine :"),
}
text = fc.read_text()
for key, (path, needle) in targets.items():
    lines = (root / path).read_text().splitlines()
    line = next(i for i, l in enumerate(lines, 1) if l.startswith(needle))
    text = text.replace(f'#L{key}"', f'#L{line}"')
text = text.replace("KitaKen1/REPO/blob/COMMIT", f"{repo}/blob/{sha}")
text = text.replace("github.com/KitaKen1/REPO)", f"github.com/{repo})")  # the [Kit26] reference
assert "REPO" not in text and "COMMIT" not in text and "#LQEX" not in text
fc.write_text(text)
print("filled", fc)

# The Lean4Web link of the top-level README.
readme = root / "README.md"
encoded = repo.replace("/", "%2F")
rtext = readme.read_text().replace("KitaKen1%2FREPO%2F", f"{encoded}%2F")
assert "%2FREPO%2F" not in rtext
readme.write_text(rtext)
print("filled", readme)
