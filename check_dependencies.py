#!/usr/bin/env python3
import os
import re
from pathlib import Path

def extract_imports(file_path):
    """Extract Gip.* imports from a Lean file"""
    imports = []
    with open(file_path, 'r') as f:
        for line in f:
            match = re.match(r'^import Gip\.(\w+)', line)
            if match:
                imports.append(match.group(1))
    return imports

def check_circular_deps():
    """Check for circular dependencies in Gip modules"""
    gip_dir = Path('Gip')
    dependencies = {}

    # Build dependency graph
    for lean_file in gip_dir.glob('*.lean'):
        module_name = lean_file.stem
        dependencies[module_name] = extract_imports(lean_file)

    # Check for circular dependencies
    def has_cycle(module, visited, rec_stack):
        visited[module] = True
        rec_stack[module] = True

        for dep in dependencies.get(module, []):
            if dep not in visited:
                if has_cycle(dep, visited, rec_stack):
                    return True
            elif rec_stack[dep]:
                print(f"Circular dependency detected: {module} -> {dep}")
                return True

        rec_stack[module] = False
        return False

    visited = {m: False for m in dependencies}
    rec_stack = {m: False for m in dependencies}

    has_any_cycle = False
    for module in dependencies:
        if not visited[module]:
            if has_cycle(module, visited, rec_stack):
                has_any_cycle = True

    if not has_any_cycle:
        print("No circular dependencies detected")

    # Print dependency summary
    print("\nDependency Summary:")
    for module, deps in sorted(dependencies.items()):
        if deps:
            print(f"{module}: {', '.join(deps)}")

if __name__ == "__main__":
    check_circular_deps()