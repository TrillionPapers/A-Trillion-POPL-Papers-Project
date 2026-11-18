#!/usr/bin/env python3
"""Writes the import graph of Lean's own library (the modules under Init, Std and Lean) to
lean-imports.txt.  Needs a Lean toolchain; `make check` does not run this script, it reads the
file that is committed.

Each line is a module: its name, then the numbers of the modules that it imports with
`public import`, with a plain `import`, and with `import all`, separated by tabs.  A module's
number is the number of its line, from 0.  `meta import` counts as `import`, and
`public meta import` as `public import`."""
import os
import re
import subprocess
import sys

prefix = subprocess.run(['lean', '--print-prefix'], capture_output=True, text=True, check=True).stdout.strip()
version = 'Lean ' + re.search(r'version ([0-9.]+)', subprocess.run(['lean', '--version'], capture_output=True, text=True, check=True).stdout).group(1)
root = os.path.join(prefix, 'src', 'lean')
pattern = re.compile(r'^(public )?(meta )?import (all )?([A-Za-z0-9_.]+)\s*$')
modules = {}
for top in ('Init', 'Std', 'Lean'):
    for directory, _, files in os.walk(os.path.join(root, top)):
        for name in files:
            if name.endswith('.lean'):
                path = os.path.join(directory, name)
                imports = []
                with open(path, encoding='utf-8') as source:
                    for line in source:
                        m = pattern.match(line)
                        if m:
                            imports.append(('all' if m.group(3) else 'pub' if m.group(1) else 'priv', m.group(4)))
                modules[os.path.relpath(path, root)[:-5].replace(os.sep, '.')] = imports
names = sorted(modules)
number = {name: i for i, name in enumerate(names)}
with open(sys.argv[1] if len(sys.argv) > 1 else 'lean-imports.txt', 'w') as out:
    out.write(f'# {version}: {len(names)} modules\n')
    for name in names:
        kinds = {kind: sorted(number[dep] for k, dep in modules[name] if k == kind and dep in number)
                 for kind in ('pub', 'priv', 'all')}
        out.write('\t'.join([name] + [' '.join(map(str, kinds[kind])) for kind in ('pub', 'priv', 'all')]) + '\n')
