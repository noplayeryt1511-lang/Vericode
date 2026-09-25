#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
VeriCode GUI
============
Eine einfache Tkinter-Oberflaeche fuer VeriCode (github.com/noplayeryt1511-lang/Vericode).

Damit kannst du:
  - links das "Legacy"-Programm auswaehlen (Sprache + Datei + Funktionsname)
  - rechts das "Migrated"-Programm auswaehlen (Sprache + Datei + Funktionsname)
  - auf "Verifizieren" klicken -> beide Seiten werden per Bridge in den
    gemeinsamen Python-Subset transpiliert und mit engine.py (Z3) verglichen.
  - das Ergebnis (PROVEN / VERIFIED-BY-TESTING / FLAGGED FOR MANUAL REVIEW)
    inkl. Gegenbeispiel wird unten angezeigt.

WICHTIG - Voraussetzungen:
  1. Das VeriCode-Repo muss lokal vorliegen, z.B.:
         git clone https://github.com/noplayeryt1511-lang/Vericode
  2. Seine Abhaengigkeiten muessen installiert sein:
         pip install -r Vericode/requirements.txt
  3. In diesem GUI unten links den Pfad zu diesem geklonten Repo eintragen
     (Ordner, der engine.py, c_bridge.py, java_bridge.py, ... enthaelt).

Unterstuetzte Quellsprachen (ueber die jeweilige Bridge des Repos): C, Java,
C#, Go, Rust. Alle Bridges sind laut Repo-README bewusst minimal gehalten:
nur int-Parameter/Rueckgabewerte, einfache Kontrollstrukturen, keine
Pointer/Structs/Arrays. COBOL ist nicht eingebunden (deutlich komplexer,
siehe full_pipeline.py im Repo fuer den vollautomatischen COBOL-Weg).

Start:
    python3 vericode_gui.py
"""

import os
import re
import sys
import traceback
import importlib
import tkinter as tk
from tkinter import ttk, filedialog, messagebox, scrolledtext

# ---------------------------------------------------------------------------
# Sprachdefinitionen: Modulname im Repo, Funktionsname im Modul, Dateiendung,
# und ob das Modul einen "python_function_name"-Parameter unterstuetzt.
# ---------------------------------------------------------------------------
LANGUAGES = {
    "C": {
        "module": "c_bridge",
        "func": "transpile_c_function",
        "ext": [("C-Dateien", "*.c *.h"), ("Alle Dateien", "*.*")],
        "supports_py_name": False,
    },
    "Java": {
        "module": "java_bridge",
        "func": "transpile_java_method",
        "ext": [("Java-Dateien", "*.java"), ("Alle Dateien", "*.*")],
        "supports_py_name": True,
    },
    "C#": {
        "module": "csharp_bridge",
        "func": "transpile_csharp_method",
        "ext": [("C#-Dateien", "*.cs"), ("Alle Dateien", "*.*")],
        "supports_py_name": True,
    },
    "Go": {
        "module": "go_bridge",
        "func": "transpile_go_function",
        "ext": [("Go-Dateien", "*.go"), ("Alle Dateien", "*.*")],
        "supports_py_name": True,
    },
    "Rust": {
        "module": "rust_bridge",
        "func": "transpile_rust_function",
        "ext": [("Rust-Dateien", "*.rs"), ("Alle Dateien", "*.*")],
        "supports_py_name": True,
    },
}

ARG_TYPES = ["Int", "Real"]

DEF_NAME_RE = re.compile(r"^def\s+([A-Za-z_][A-Za-z0-9_]*)\s*\(", re.MULTILINE)


class UnsupportedConstructWrapper(Exception):
    pass


class ProgramPanel(ttk.LabelFrame):
    """Ein Auswahlblock (Sprache, Datei, Funktion, optionale Parameter)."""

    def __init__(self, master, title):
        super().__init__(master, text=title, padding=10)

        ttk.Label(self, text="Sprache:").grid(row=0, column=0, sticky="w", pady=2)
        self.language_var = tk.StringVar(value="C")
        self.language_combo = ttk.Combobox(
            self, textvariable=self.language_var, values=list(LANGUAGES.keys()),
            state="readonly", width=20
        )
        self.language_combo.grid(row=0, column=1, columnspan=2, sticky="we", pady=2)

        ttk.Label(self, text="Datei:").grid(row=1, column=0, sticky="w", pady=2)
        self.file_var = tk.StringVar()
        ttk.Entry(self, textvariable=self.file_var, width=32).grid(
            row=1, column=1, sticky="we", pady=2
        )
        ttk.Button(self, text="...", width=3, command=self._browse).grid(
            row=1, column=2, padx=(4, 0)
        )

        ttk.Label(self, text="Funktion/Methode:").grid(row=2, column=0, sticky="w", pady=2)
        self.func_var = tk.StringVar()
        ttk.Entry(self, textvariable=self.func_var, width=32).grid(
            row=2, column=1, columnspan=2, sticky="we", pady=2
        )

        ttk.Label(self, text="Parameternamen (optional,\nkomma-getrennt):").grid(
            row=3, column=0, sticky="w", pady=2
        )
        self.params_var = tk.StringVar()
        ttk.Entry(self, textvariable=self.params_var, width=32).grid(
            row=3, column=1, columnspan=2, sticky="we", pady=2
        )

        self.columnconfigure(1, weight=1)

    def _browse(self):
        lang = self.language_var.get()
        filetypes = LANGUAGES[lang]["ext"]
        path = filedialog.askopenfilename(title="Quelldatei waehlen", filetypes=filetypes)
        if path:
            self.file_var.set(path)
            if not self.func_var.get():
                base = os.path.splitext(os.path.basename(path))[0]
                self.func_var.set(base)

    def get_config(self):
        raw_params = self.params_var.get().strip()
        param_names = [p.strip() for p in raw_params.split(",") if p.strip()] or None
        return {
            "language": self.language_var.get(),
            "file": self.file_var.get().strip(),
            "function": self.func_var.get().strip(),
            "param_names": param_names,
        }


class VeriCodeGUI(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("VeriCode GUI")
        self.geometry("900x720")
        self.repo_modules = {}  # lazily imported bridge/engine modules

        # --- Repo-Pfad -------------------------------------------------
        repo_frame = ttk.Frame(self, padding=(10, 10, 10, 0))
        repo_frame.pack(fill="x")
        ttk.Label(repo_frame, text="Pfad zum VeriCode-Repo:").pack(side="left")
        self.repo_path_var = tk.StringVar(value=os.getcwd())
        ttk.Entry(repo_frame, textvariable=self.repo_path_var).pack(
            side="left", fill="x", expand=True, padx=6
        )
        ttk.Button(repo_frame, text="...", width=3, command=self._browse_repo).pack(side="left")

        # --- Legacy / Migrated Panels -----------------------------------
        panels_frame = ttk.Frame(self, padding=10)
        panels_frame.pack(fill="x")
        panels_frame.columnconfigure(0, weight=1)
        panels_frame.columnconfigure(1, weight=1)

        self.legacy_panel = ProgramPanel(panels_frame, "Legacy-Programm")
        self.legacy_panel.grid(row=0, column=0, sticky="nsew", padx=(0, 5))

        self.migrated_panel = ProgramPanel(panels_frame, "Migriertes Programm")
        self.migrated_panel.grid(row=0, column=1, sticky="nsew", padx=(5, 0))

        # --- Optionen ----------------------------------------------------
        options_frame = ttk.Frame(self, padding=(10, 0, 10, 10))
        options_frame.pack(fill="x")

        ttk.Label(options_frame, text="Werttyp (arg_type):").pack(side="left")
        self.arg_type_var = tk.StringVar(value="Int")
        ttk.Combobox(
            options_frame, textvariable=self.arg_type_var, values=ARG_TYPES,
            state="readonly", width=8
        ).pack(side="left", padx=(4, 20))

        ttk.Label(options_frame, text="Fuzz-Samples (Fallback):").pack(side="left")
        self.fuzz_var = tk.StringVar(value="200000")
        ttk.Entry(options_frame, textvariable=self.fuzz_var, width=10).pack(side="left", padx=4)

        self.verify_btn = ttk.Button(
            options_frame, text="Verifizieren", command=self._run_verify
        )
        self.verify_btn.pack(side="right")

        # --- Output --------------------------------------------------------
        out_frame = ttk.LabelFrame(self, text="Ergebnis", padding=10)
        out_frame.pack(fill="both", expand=True, padx=10, pady=(0, 10))
        self.output = scrolledtext.ScrolledText(out_frame, wrap="word", font=("Consolas", 10))
        self.output.pack(fill="both", expand=True)

    def _browse_repo(self):
        path = filedialog.askdirectory(title="VeriCode-Repo-Ordner waehlen")
        if path:
            self.repo_path_var.set(path)

    def _log(self, text, clear=False):
        if clear:
            self.output.delete("1.0", "end")
        self.output.insert("end", text + "\n")
        self.output.see("end")
        self.update_idletasks()

    def _ensure_repo_on_path(self):
        repo_path = self.repo_path_var.get().strip()
        if not repo_path or not os.path.isdir(repo_path):
            raise RuntimeError(f"Repo-Pfad nicht gefunden: {repo_path!r}")
        if repo_path not in sys.path:
            sys.path.insert(0, repo_path)

    def _get_module(self, module_name):
        if module_name not in self.repo_modules:
            self.repo_modules[module_name] = importlib.import_module(module_name)
        else:
            importlib.reload(self.repo_modules[module_name])
        return self.repo_modules[module_name]

    def _transpile_side(self, cfg, label):
        lang_info = LANGUAGES[cfg["language"]]
        if not cfg["file"] or not os.path.isfile(cfg["file"]):
            raise RuntimeError(f"[{label}] Datei nicht gefunden: {cfg['file']!r}")
        if not cfg["function"]:
            raise RuntimeError(f"[{label}] Kein Funktions-/Methodenname angegeben.")

        with open(cfg["file"], "r", encoding="utf-8") as f:
            source = f.read()

        module = self._get_module(lang_info["module"])
        func = getattr(module, lang_info["func"])

        kwargs = {"param_names": cfg["param_names"]}
        if lang_info["supports_py_name"]:
            kwargs["python_function_name"] = f"_{label}_fn"

        self._log(f"[{label}] Transpiliere {cfg['function']} ({cfg['language']}) ...")
        py_source = func(source, cfg["function"], **kwargs)
        self._log(f"[{label}] Erzeugter Python-Code:\n{py_source}")

        match = DEF_NAME_RE.search(py_source)
        if not match:
            raise RuntimeError(f"[{label}] Konnte keine erzeugte Funktion im Python-Code finden.")
        fn_name = match.group(1)

        namespace = {}
        exec(compile(py_source, f"<{label}>", "exec"), namespace)
        return namespace[fn_name]

    def _run_verify(self):
        self.verify_btn.state(["disabled"])
        try:
            self._log("=" * 70, clear=True)
            self._ensure_repo_on_path()
            engine = self._get_module("engine")
            import z3  # noqa: F401  (nur um Import-Fehler frueh + klar zu melden)

            legacy_cfg = self.legacy_panel.get_config()
            migrated_cfg = self.migrated_panel.get_config()

            legacy_fn = self._transpile_side(legacy_cfg, "legacy")
            migrated_fn = self._transpile_side(migrated_cfg, "migrated")

            arg_type = z3.IntSort() if self.arg_type_var.get() == "Int" else z3.RealSort()
            try:
                fuzz_samples = int(self.fuzz_var.get())
            except ValueError:
                fuzz_samples = 200_000

            self._log("Starte Verifikation mit engine.verify() ...")
            result = engine.verify(
                legacy_fn, migrated_fn, arg_type=arg_type, fuzz_samples=fuzz_samples
            )

            self._log("-" * 70)
            self._log(f"Ergebnis: {result.label}")
            counterexample = getattr(result, "counterexample", None)
            if counterexample:
                self._log(f"Gegenbeispiel: {counterexample}")
            else:
                self._log("Kein Gegenbeispiel gefunden.")

        except Exception:
            self._log("FEHLER:\n" + traceback.format_exc())
            messagebox.showerror("Fehler", "Bei der Verifikation ist ein Fehler aufgetreten. Details unten im Ergebnisfeld.")
        finally:
            self.verify_btn.state(["!disabled"])


if __name__ == "__main__":
    app = VeriCodeGUI()
    app.mainloop()
