#!/usr/bin/env python3
"""Build the mathematical website from handwritten pages and the actual Lean statement."""
import html
import json
import os
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
PAGES = {"index": "Overview", "statement": "Statement", "proof": "Proof guide",
         "library": "Library", "api": "API", "verification": "Verification"}
DECLARATIONS = [
    ("theoremA", "MainTheorems", "Theorem A (Theorem 4.4): image-closed subcategories are the intersections T ∩ F of pretorsion theories, and the subcategories with Z = Gen Z ∩ Cogen Z"),
    ("completeLattice", "MainTheorems", "Theorem 3.6: the pretorsion theories of mod Λ form a complete lattice, with meets (3.2) and joins (3.3)"),
    ("gandhiPretorsion", "MainTheorems", "Theorem 7.5: pretorsion theories of the linear quiver are counted by q-Gandhi polynomials of the first kind"),
    ("gandhiImageClosed", "MainTheorems", "Theorem 8.5: image-closed subcategories of the linear quiver are counted by q-Gandhi polynomials of the second kind"),
    ("theoremBPretorsion", "MainTheorems", "Theorem B, first identity"),
    ("theoremBImageClosed", "MainTheorems", "Theorem B, second identity"),
    ("Statement.isPretorsionTheory_iff_traceRejectCondition", "Pretorsion/TraceReject", "Theorem 2.12: the trace-reject criterion for pretorsion theories"),
    ("Statement.isPretorsionTheory_iInf", "Pretorsion/Partners", "Proposition 3.2: second components with a fixed first component are closed under intersections"),
    ("Statement.PretorsionTheory.sInf_middle", "Pretorsion/FixedMiddle", "Proposition 3.8: meets keep a fixed intersection"),
    ("Statement.isTorsionPair_iff", "Pretorsion/TorsionPairs", "Proposition 2.5: torsion pairs are the pretorsion theories with zero intersection"),
    ("Statement.realization_bounds", "Realizations/LeastRealization", "Corollaries 4.5 and 4.7: least and greatest realizations of an image-closed subcategory"),
    ("theorem_4_11", "IndecomposableClosures/FiniteDimensionalAlgebras", "Theorem 4.11: image closure is a finitary convex geometry on ind Λ"),
    ("LinearQuiver.isImageClosed_iff_intersectionClosed", "LinearQuiver/ImageClosed", "Theorem 5.5: image-closed subcategories of mod Λ_n are the intersection-closed interval families"),
    ("LinearQuiver.isPretorsionTheory_iff_criterion", "LinearQuiver/CutoffCriterion", "Theorem 6.5: the cutoff criterion for pretorsion theories of mod Λ_n"),
]


def main():
    subprocess.run(["python3", str(ROOT / "scripts/generate_challenge.py"), "--check"], check=True)
    commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    dirty = bool(subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT, text=True))
    repo_url = "https://github.com/haruhisa-enomoto/pretorsion-image-closed"
    source_url = repo_url + "/blob/" + ("main" if dirty else commit)
    statement = (ROOT / "Challenge.lean").read_text()
    output = ROOT / "_site"
    output.mkdir(exist_ok=True)
    shutil.copytree(ROOT / "website/assets", output / "assets", dirs_exist_ok=True)
    api = ROOT / "docbuild/.lake/build/doc"
    api_state_path = ROOT / "docbuild/.lake/build/api-build.json"
    api_state = json.loads(api_state_path.read_text()) if api_state_path.exists() else {}
    has_api = (api / "index.html").exists() and api_state.get("complete", False)
    if has_api:
        for revisions in ([api_state["source_commit"], "HEAD"], ["HEAD"]):
            subprocess.run(["git", "diff", "--exit-code", *revisions, "--",
                            "PretorsionImageClosed.lean", "PretorsionImageClosed",
                            "lean-toolchain", "lake-manifest.json"],
                           cwd=ROOT, check=True)
        # A source migration can delete modules; discard stale generated pages.
        if (output / "api").exists():
            shutil.rmtree(output / "api")
        shutil.copytree(api, output / "api")
        for page in (output / "api").rglob("*.html"):
            overview = Path(os.path.relpath(output / "index.html", page.parent)).as_posix()
            page.write_text(page.read_text().replace(
                "<span>Documentation</span>",
                f'<span><a href="{overview}">Pretorsion theories and image-closed subcategories</a></span>', 1))
    elif (output / "api").exists():
        shutil.rmtree(output / "api")
    status_file = ROOT / "verification-status.json"
    status = json.loads(status_file.read_text()) if status_file.exists() else {}
    rows = []
    for declaration, module, description in DECLARATIONS:
        path = "PretorsionImageClosed/" + module
        target = ("api/" + path + ".html#PretorsionImageClosed." + declaration) if has_api else source_url + "/" + path + ".lean"
        rows.append(f'<tr><td><a href="{target}"><code>{declaration}</code></a></td><td>{description}</td></tr>')
    replacements = {
        "source_url": source_url,
        "repo_url": repo_url,
        "statement": html.escape(statement),
        "statement_lines": str(len(statement.splitlines())),
        "declaration_rows": "".join(rows),
        "api_link": '<p><a href="api/index.html">Browse and search the generated API</a></p>' if has_api else
                    '<p>The API has not been generated in this preview. Follow <code>docbuild/README.md</code> to build the documentation tool, run <code>python3 scripts/build_api.py</code>, then rebuild this site.</p>',
        "verification_status": html.escape(status.get("summary", "Verification records are available in the repository.")),
    }
    nav = "".join(f'<a href="{slug}.html">{label}</a>' for slug, label in PAGES.items())
    nav += f'<a href="{repo_url}">GitHub</a>'
    revision = f'<a href="{repo_url}/tree/{commit}">{commit[:7]}</a>' + (" (preview)" if dirty else "")
    api_revision = (f' · API: <a href="{repo_url}/tree/{api_state["source_commit"]}">{api_state["source_commit"][:7]}</a>') if has_api else ""
    for slug, title in PAGES.items():
        body = (ROOT / f"website/pages/{slug}.html").read_text()
        for key, value in replacements.items():
            body = body.replace("{{" + key + "}}", value)
        if "{{" in body:
            raise SystemExit(f"Unresolved template value in {slug}")
        page = f'''<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>{title} · Pretorsion theories and image-closed subcategories</title><link rel="stylesheet" href="assets/site.css"></head>
<body><a class="skip" href="#main">Skip to content</a><header class="site-header"><nav class="nav" aria-label="Main"><a class="brand" href="index.html">Pretorsion theories and image-closed subcategories</a>{nav}</nav></header>
<main id="main">{body}</main><footer class="site-footer">Source: {revision}{api_revision}<br>Haruhisa Enomoto · Lean formalization · Apache-2.0</footer></body></html>'''
        (output / f"{slug}.html").write_text(page)
    (output / "build.json").write_text(json.dumps({"commit": commit, "dirty": dirty,
        "api_generated": has_api, "api_source_commit": api_state.get("source_commit") if has_api else None,
        "statement_lines": len(statement.splitlines())}, indent=2) + "\n")
    print(f"Built {len(PAGES)} pages in {output}")


if __name__ == "__main__":
    main()
