using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Covering;

internal sealed class FixedCollisionExceptionsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Covering/FixedCollisionExceptions.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "In a distinct odd cover with no modulus divisible by 27, minimality of "
            + "the modulus sum at its class count forces at most two fixed originals "
            + "to meet every ordinary-prime collision at a fixed modulo-9 word "
            + "and modulo-5 root.",
        H("Fixed Collision Exceptions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("collision-top-originals"),
                DeclarationHandle.Create(Prefix + "collisionTop"),
                H("Originals at a fixed word and root"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An original belongs to the selected group when its modulus "
                    + "is divisible by 45, its residue agrees with u modulo 9, "
                    + "and its residue agrees with omega modulo 5. Every positive "
                    + "five depth is included, with all other prime factors retained."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ordinary-prime-collision"),
                DeclarationHandle.Create(Prefix + "ordinaryPrimeCollision"),
                H("Literal prime collisions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two distinct original labels collide when some prime other "
                    + "than 3 and 5 divides both moduli and their actual residues "
                    + "agree modulo that prime. This condition does not require "
                    + "a point in the intersection of their full congruence classes."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fresh-four-slot-descent"),
                DeclarationHandle.Create(Prefix + "fresh_four_slot_descent"),
                H("Four fresh classes with smaller total modulus"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Choose four distinct originals in a cover whose modulus sum "
                    + "is minimal among all covers with the same class count. "
                    + "Four distinct fresh odd moduli greater than one cannot "
                    + "have a smaller total modulus while their congruence "
                    + "classes cover every point of the four removed classes. "
                    + "Retaining all other originals would give a cheaper cover "
                    + "with the same number of classes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("distinct-positive-multiples-pair"),
                DeclarationHandle.Create(Prefix + "distinct_positive_multiples_pair"),
                H("Two distinct positive multiples"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If distinct positive natural numbers a and b are divisible "
                    + "by d, then their sum is at least 3d. This bound supplies "
                    + "the strict cost comparison when two collision pairs use "
                    + "the same prime."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("collision-prime-arithmetic"),
                DeclarationHandle.Create(Prefix + "collision_prime_arithmetic"),
                H("Arithmetic of an ordinary prime divisor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A prime divisor p of an original odd modulus, different "
                    + "from 3 and 5, is odd, is at least 5, and is coprime to "
                    + "27, 45 and 5. These arithmetic facts are used by the "
                    + "four-slot collision descent and by the ternary-height "
                    + "prime-root capacity construction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("no-disjoint-ordinary-prime-collisions"),
                DeclarationHandle.Create(Prefix + "no_disjoint_ordinary_prime_collisions"),
                H("A four-slot replacement excludes disjoint collisions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let F cover every natural number with L congruence classes "
                        + "of pairwise distinct odd moduli greater than one. Suppose "
                        + "no modulus is divisible by 27, and the sum of its moduli "
                        + "is minimal among all such covers with L classes. The "
                        + "comparison covers have no restriction on prime heights. "
                        + "Then four distinct originals in one selected group cannot "
                        + "form two disjoint prime-collision pairs.")),
                    Paragraph(Text(
                        "For collision primes p and r that differ, replace the four "
                        + "originals by classes of moduli 27, 135, 27p and 27r. "
                        + "The three extensions of u modulo 27 assign the first "
                        + "two rows, or select a final row using the actual prime "
                        + "phase of the appropriate original pair.")),
                    Paragraph(Text(
                        "If the collision primes coincide, use moduli 27, 135, "
                        + "27p and 135p. The phases of the two collision pairs may "
                        + "differ. In both cases every point of every removed "
                        + "congruence class lies in a replacement class. All other "
                        + "originals are retained, and divisibility by 27 makes "
                        + "all four new moduli globally fresh.")),
                    Paragraph(Text(
                        "For distinct p and r the old four-modulus sum is at "
                        + "least 90(p+r), while the new sum is 27(6+p+r). "
                        + "For equal primes, distinct positive multiples of 45p "
                        + "give an old sum of at least 225p, while the new sum "
                        + "is 162(1+p). Each replacement strictly lowers the sum "
                        + "without changing L, contradicting minimality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fixed-collision-exceptions"),
                DeclarationHandle.Create(Prefix + "exists_fixed_collision_exceptions"),
                H("One exception set works for every source point"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Under the same assumptions, for every u and omega there "
                        + "is a set X of at most two original labels in the selected "
                        + "group such that no two labels outside X have an "
                        + "ordinary-prime collision. If a collision exists, its "
                        + "two endpoints form X; otherwise X is empty.")),
                    Paragraph(Text(
                        "The choice of X precedes every cofactor point and "
                        + "probability law. Its labels remain in the original "
                        + "cover. The theorem does not assume minimal class count, "
                        + "does not restrict five depths, and does not assert "
                        + "noncoverage for arbitrary odd distinct families."))),
                DescribeRole.Theorem))));
}
