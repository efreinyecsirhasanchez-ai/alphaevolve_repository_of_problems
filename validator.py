"""Data integrity validator for AlphaEvolve problem repository.

This script validates the status.json file to ensure:
- All 67 problems are accounted for
- No duplicate entries across categories
- Valid problem number ranges (1-67)
- Proper JSON structure
- Summary statistics
"""

import json
import sys
from pathlib import Path
from typing import Dict, List, Set, Tuple


class ProblemValidator:
    """Validates the integrity of problem data."""
    
    TOTAL_PROBLEMS = 67
    STATUS_FILE = "status.json"
    VALID_CATEGORIES = {
        "world_record",
        "former_record", 
        "worse_than_record",
        "matched_optimal"
    }
    
    def __init__(self):
        """Initialize validator."""
        self.data = None
        self.errors = []
        self.warnings = []
        self.stats = {
            "total_categorized": 0,
            "total_uncategorized": 0,
            "by_category": {}
        }
    
    def load_data(self) -> bool:
        """Load and parse status.json file.
        
        Returns:
            bool: True if file loaded successfully, False otherwise.
        """
        try:
            with open(self.STATUS_FILE, "r") as f:
                self.data = json.load(f)
            return True
        except FileNotFoundError:
            self.errors.append(f"❌ File not found: {self.STATUS_FILE}")
            return False
        except json.JSONDecodeError as e:
            self.errors.append(f"❌ Invalid JSON: {e}")
            return False
    
    def validate_structure(self) -> bool:
        """Validate JSON structure and categories.
        
        Returns:
            bool: True if structure is valid, False otherwise.
        """
        if not isinstance(self.data, dict):
            self.errors.append("❌ Data must be a dictionary (JSON object)")
            return False
        
        # Check for invalid categories
        invalid_cats = set(self.data.keys()) - self.VALID_CATEGORIES
        if invalid_cats:
            self.errors.append(
                f"❌ Invalid categories found: {', '.join(invalid_cats)}"
            )
            return False
        
        # Check that all values are lists
        for category, problems in self.data.items():
            if not isinstance(problems, list):
                self.errors.append(
                    f"❌ Category '{category}' must contain a list, "
                    f"got {type(problems).__name__}"
                )
                return False
        
        return True
    
    def validate_problem_numbers(self) -> bool:
        """Validate problem numbers are in valid range.
        
        Returns:
            bool: True if all numbers are valid, False otherwise.
        """
        all_problems: Set[int] = set()
        
        for category, problems in self.data.items():
            for problem in problems:
                # Check type
                if not isinstance(problem, int):
                    self.errors.append(
                        f"❌ Category '{category}' contains non-integer: {problem}"
                    )
                    return False
                
                # Check range
                if problem < 1 or problem > self.TOTAL_PROBLEMS:
                    self.errors.append(
                        f"❌ Problem number {problem} out of range "
                        f"(must be 1-{self.TOTAL_PROBLEMS})"
                    )
                    return False
                
                all_problems.add(problem)
        
        return True
    
    def check_duplicates(self) -> bool:
        """Check for duplicate problem entries across categories.
        
        Returns:
            bool: True if no duplicates, False otherwise.
        """
        problem_to_categories: Dict[int, List[str]] = {}
        
        for category, problems in self.data.items():
            for problem in problems:
                if problem not in problem_to_categories:
                    problem_to_categories[problem] = []
                problem_to_categories[problem].append(category)
        
        # Find duplicates
        duplicates_found = False
        for problem, categories in problem_to_categories.items():
            if len(categories) > 1:
                self.errors.append(
                    f"❌ Problem {problem} appears in multiple categories: "
                    f"{', '.join(categories)}"
                )
                duplicates_found = True
        
        return not duplicates_found
    
    def find_uncategorized(self) -> Tuple[int, List[int]]:
        """Find problems not categorized in any category.
        
        Returns:
            Tuple of (count, list of problem numbers).
        """
        all_categorized = set()
        for problems in self.data.values():
            all_categorized.update(problems)
        
        all_problems = set(range(1, self.TOTAL_PROBLEMS + 1))
        uncategorized = sorted(all_problems - all_categorized)
        
        return len(uncategorized), uncategorized
    
    def calculate_statistics(self) -> Dict:
        """Calculate statistics about the problems.
        
        Returns:
            Dictionary with statistics.
        """
        uncategorized_count, uncategorized_list = self.find_uncategorized()
        
        stats = {
            "total_problems": self.TOTAL_PROBLEMS,
            "total_categorized": self.TOTAL_PROBLEMS - uncategorized_count,
            "total_uncategorized": uncategorized_count,
            "uncategorized_problems": uncategorized_list,
            "by_category": {}
        }
        
        for category in self.VALID_CATEGORIES:
            count = len(self.data.get(category, []))
            stats["by_category"][category] = count
        
        return stats
    
    def validate(self) -> bool:
        """Run all validations.
        
        Returns:
            bool: True if all validations pass, False otherwise.
        """
        print("🔍 Starting validation...\n")
        
        # Load data
        if not self.load_data():
            return False
        
        # Run validations
        validations = [
            ("Structure", self.validate_structure),
            ("Problem Numbers", self.validate_problem_numbers),
            ("Duplicates", self.check_duplicates),
        ]
        
        all_passed = True
        for name, validator_func in validations:
            result = validator_func()
            status = "✅" if result else "❌"
            print(f"{status} {name} check")
            if not result:
                all_passed = False
        
        return all_passed
    
    def report(self) -> None:
        """Print validation report."""
        print("\n" + "="*60)
        print("📊 VALIDATION REPORT")
        print("="*60 + "\n")
        
        # Errors
        if self.errors:
            print("❌ ERRORS:")
            for error in self.errors:
                print(f"  {error}")
            print()
        
        # Warnings
        if self.warnings:
            print("⚠️  WARNINGS:")
            for warning in self.warnings:
                print(f"  {warning}")
            print()
        
        # Statistics
        stats = self.calculate_statistics()
        print("📈 STATISTICS:")
        print(f"  Total Problems: {stats['total_problems']}")
        print(f"  Categorized: {stats['total_categorized']}")
        print(f"  Uncategorized: {stats['total_uncategorized']}")
        print()
        
        print("📂 BY CATEGORY:")
        for category, count in stats["by_category"].items():
            print(f"  • {category}: {count}")
        print()
        
        if stats["uncategorized_problems"]:
            print(f"❓ UNCATEGORIZED PROBLEMS ({len(stats['uncategorized_problems'])}):")
            # Print in groups of 10 for readability
            uncategorized = stats["uncategorized_problems"]
            for i in range(0, len(uncategorized), 10):
                batch = uncategorized[i:i+10]
                print(f"  {', '.join(map(str, batch))}")
            print()
        
        # Summary
        print("="*60)
        if not self.errors and not self.warnings:
            print("✅ VALIDATION PASSED - All checks successful!")
            print("="*60)
            return True
        elif self.errors:
            print("❌ VALIDATION FAILED - See errors above")
            print("="*60)
            return False
        else:
            print("⚠️  VALIDATION PASSED WITH WARNINGS")
            print("="*60)
            return True


def main() -> int:
    """Main entry point.
    
    Returns:
        Exit code (0 for success, 1 for failure).
    """
    validator = ProblemValidator()
    is_valid = validator.validate()
    validator.report()
    return 0 if is_valid and not validator.errors else 1


if __name__ == "__main__":
    sys.exit(main())
