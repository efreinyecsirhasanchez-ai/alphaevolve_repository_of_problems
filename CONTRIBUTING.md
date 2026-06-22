# Contributing to AlphaEvolve Repository

Thank you for your interest in contributing to this repository! We welcome contributions of all kinds: bug reports, feature requests, documentation improvements, and code enhancements.

## 📋 Table of Contents

- [Code of Conduct](#code-of-conduct)
- [Getting Started](#getting-started)
- [How to Contribute](#how-to-contribute)
- [Reporting Issues](#reporting-issues)
- [Submitting Changes](#submitting-changes)
- [Style Guide](#style-guide)
- [Recognition](#recognition)

---

## Code of Conduct

This project follows [Google's Open Source Community Guidelines](https://opensource.google/conduct/). Be respectful, inclusive, and professional in all interactions.

## Contributor License Agreement

Contributions to this project must be accompanied by a Contributor License Agreement. You (or your employer) retain the copyright to your contribution, this simply gives us permission to use and redistribute your contributions as part of the project. Head over to <https://cla.developers.google.com/> to see your current agreements on file or to sign a new one.

You generally only need to submit a CLA once, so if you've already submitted one (even if it was for a different project), you probably don't need to do it again.

---

## Getting Started

### Prerequisites

- Git
- Python 3.8+
- GitHub account

### Local Setup

1. **Fork the repository**
   ```bash
   # Visit https://github.com/efreinyecsirhasanchez-ai/alphaevolve_repository_of_problems
   # Click "Fork" button
   ```

2. **Clone your fork**
   ```bash
   git clone https://github.com/YOUR_USERNAME/alphaevolve_repository_of_problems.git
   cd alphaevolve_repository_of_problems
   ```

3. **Add upstream remote**
   ```bash
   git remote add upstream https://github.com/efreinyecsirhasanchez-ai/alphaevolve_repository_of_problems.git
   ```

4. **Create a virtual environment**
   ```bash
   python -m venv venv
   source venv/bin/activate  # On Windows: venv\Scripts\activate
   ```

5. **Install dependencies** (if needed)
   ```bash
   pip install matplotlib
   ```

---

## How to Contribute

### 1. Create an Issue First

For bugs or features, please create an issue first:

- **Bug Report**: Describe the issue, steps to reproduce, and expected behavior
- **Feature Request**: Explain the feature and why it would be useful
- **Documentation**: Suggest improvements to existing docs

### 2. Work on Your Change

```bash
# Update main branch
git fetch upstream
git checkout main
git merge upstream/main

# Create feature branch
git checkout -b feature/your-feature-name
```

**Branch naming conventions:**
- `feature/` - New features
- `bugfix/` - Bug fixes
- `docs/` - Documentation updates
- `test/` - Test additions
- `refactor/` - Code refactoring

### 3. Make Your Changes

Ensure your changes:
- Follow the [Style Guide](#style-guide)
- Pass all tests: `python validator.py`
- Don't break existing functionality

### 4. Commit Your Changes

```bash
git add .
git commit -m "type: Brief description

Optional longer description explaining the changes.
- Bullet point 1
- Bullet point 2
"
```

**Commit message format:**
```
type(scope): subject

body

footer
```

**Types:** `feat`, `fix`, `docs`, `style`, `refactor`, `test`, `chore`

**Examples:**
```
feat(validator): Add duplicate checking in validation

fix(generate_image.py): Correct color rendering in dark mode

docs(CONTRIBUTING): Update setup instructions
```

### 5. Push Your Changes

```bash
git push origin feature/your-feature-name
```

### 6. Create a Pull Request

We use GitHub pull requests for code reviews. Consult [GitHub Help](https://help.github.com/articles/about-pull-requests/) for more information on using pull requests.

1. Go to GitHub and click "Compare & pull request"
2. Fill in the PR template:
   - **Title**: Brief description
   - **Description**: What changed and why
   - **Related Issue**: Link to related issue (if any)
   - **Testing**: How was this tested?
3. Request review from maintainers

**All submissions, including submissions by project members, require review.**

---

## Reporting Issues

Use GitHub Issues to report problems. Include:

### Bug Report Template

```markdown
## Description
Brief description of the bug.

## Steps to Reproduce
1. Step 1
2. Step 2
3. Step 3

## Expected Behavior
What should happen?

## Actual Behavior
What actually happened?

## Environment
- Python version: X.X.X
- OS: Windows/Mac/Linux
- Branch: main

## Additional Context
Any additional information.
```

### Feature Request Template

```markdown
## Description
Brief description of the requested feature.

## Motivation
Why would this feature be useful?

## Proposed Solution
How should it work?

## Alternatives Considered
Other possible approaches?

## Additional Context
Any additional information.
```

---

## Submitting Changes

### Code Review Process

1. **Automated Checks**
   - ✅ All tests pass
   - ✅ Code style validated
   - ✅ No conflicts with main

2. **Human Review**
   - At least one maintainer reviews
   - Changes requested or approved
   - Author responds to feedback

3. **Merge**
   - Squash commits if multiple
   - Merge to main branch
   - Delete feature branch

### Before Submitting

- [ ] Code follows style guide
- [ ] All tests pass (`python validator.py`)
- [ ] New features have tests
- [ ] Documentation is updated
- [ ] Commit messages are clear
- [ ] No large binary files added
- [ ] No credentials or sensitive data included

---

## Style Guide

### Python Code

- **Line length**: Max 88 characters
- **Indentation**: 4 spaces
- **Naming**:
  - `snake_case` for variables and functions
  - `CamelCase` for classes
  - `UPPER_CASE` for constants

### Example

```python
"""Module docstring."""

import json
from typing import Dict, List

TOTAL_PROBLEMS = 67  # Constants in UPPER_CASE


class ProblemValidator:  # CamelCase for classes
    """Class docstring."""
    
    def validate_data(self):  # snake_case for methods
        """Method docstring."""
        valid_problems = []  # snake_case for variables
        return valid_problems
```

### Documentation

- Use Markdown for all documentation
- Include code examples where helpful
- Keep line length under 80 characters
- Use clear, concise language

### JSON

```json
{
  "world_record": [1, 2, 3],
  "former_record": [4, 5]
}
```

- Use 2-space indentation
- Use lowercase keys
- Include comments when helpful

---

## Project Structure

```
alphaevolve_repository_of_problems/
├── README.md                 # Project overview
├── CONTRIBUTING.md           # This file
├── TODOS.md                  # Roadmap and task tracking
├── LICENSE                   # Apache 2.0 license
├── .github/                  # GitHub workflows
├── generate_image.py         # Visualization generator
├── validator.py              # Data validation script
├── status.json               # Problem status data
├── problems/                 # Problem definitions
├── experiments/              # Experiment results
└── .gitignore                # Git ignore rules
```

---

## Common Tasks

### Run Validation

```bash
python validator.py
```

### Generate Visualizations

```bash
python generate_image.py
```

### Update Status Data

Edit `status.json` following this structure:

```json
{
  "world_record": [list of problem numbers],
  "former_record": [list of problem numbers],
  "worse_than_record": [list of problem numbers],
  "matched_optimal": [list of problem numbers]
}
```

Then run validator: `python validator.py`

---

## Need Help?

- 💬 **Questions**: Open a Discussion or Issue
- 🐛 **Bug**: Create a Bug Report issue
- 💡 **Ideas**: Share in Discussions
- 📖 **Documentation**: Review README.md

---

## Recognition

Contributors will be recognized in:
- GitHub contributors list
- Release notes (for significant contributions)
- Project acknowledgments

---

## License

By contributing, you agree that your contributions will be licensed under the Apache License 2.0 (for code) or CC-BY 4.0 (for other materials), consistent with the project license.

---

**Thank you for contributing! 🙏**

For more information, see:
- [Original AlphaEvolve Project](https://arxiv.org/abs/2511.02864)
- [Google DeepMind Research](https://deepmind.google/)
