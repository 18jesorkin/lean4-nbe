# Project

This is an implementation of Normalization-By-Evaluation in Lean4 from the ([PDF](Leicester.pdf)) slide notes.

Currently what is formalized is:

- Normalization-By-Eval for Monoid-rewriting (Slides 25-35)

- Normalization-By-Eval for Godel's system T (Slides 62-70)

# Build and view Verso-textbook

## Using the Makefile

Run `make show`.
If everything works this will build and open the textbook in your browser.

## Step by step

To build the Verso-textbook documenting the code:

1. Run `lake exe cache get`:

    This makes it so mathlib is quick to build.

2. Run `lake build`:

    This builds the code.

3. Run `lake exe textbook`

    This write the textbook version into the `_out` directory.

    This will take the verso code from `Lean4Nbe/Textbook.lean`, build
    the textbook from it and put the result in the `_out` directory.

4. Run `python3 -m http.server 8880 --directory _out/html-single`:

    This creates a local server where you can read the textbook that was built.

6. View the textbook in your browser with `http://localhost:8880/`
