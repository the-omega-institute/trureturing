using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class InversePowerLineBasicsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/StatisticalMechanics/InversePowerLineBasics";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Asymptotics/ferudun2026inversepowerline");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Inverse-power equilibrium rigidity on the real line.",
        H("Inverse-power line: Basics"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("is-sequilibrium"),
                DeclarationHandle.Create(Module + ".IsSEquilibrium"),
                H("IsSEquilibrium"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Thin, Parenthesized(Seq(F.Id("s"), Thin, Colon, Thin, Seq(Mathbb, Grp(F.Id("R"))))), Thin, Comma, Thin, Forall, Thin, Parenthesized(Seq(F.Id("X"), Thin, Colon, Thin, Seq(Operatorname, Grp(F.Id("Set"))), Thin, Seq(Mathbb, Grp(F.Id("R"))))), Thin, Comma, Thin, Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("IsSEquilibrium"))), Thin, F.Id("s"), Thin, F.Id("X"), Thin, Iff, Thin, D(1), Thin, Lt, Thin, F.Id("s"), Thin, Land, Thin, F.Id("X"), Thin, Dot, Thin, Seq(Operatorname, Grp(F.Id("Nontrivial"))), Thin, Land, Thin, Parenthesized(Seq(Forall, Thin, F.Id("u"), Thin, F.Id("v"), Thin, Colon, Thin, Seq(Mathbb, Grp(F.Id("R"))), Thin, Comma, Thin, Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("Set"))), Thin, Dot, Thin, Seq(Operatorname, Grp(F.Id("inter"))), Thin, F.Id("X"), Thin, Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("Set"))), Thin, Dot, Thin, Seq(Operatorname, Grp(F.Id("Icc"))), Thin, F.Id("u"), Thin, F.Id("v"))))), Thin, Dot, Thin, Seq(Operatorname, Grp(F.Id("Finite"))))), Thin, Land, Thin, Parenthesized(Seq(Forall, Thin, F.Id("x"), Thin, Colon, Thin, Seq(Mathbb, Grp(F.Id("R"))), Thin, Comma, Thin, F.Id("x"), Thin, InMacro, Thin, F.Id("X"), Thin, To, Thin, Seq(Operatorname, Grp(F.Id("Summable"))), Thin, Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("fun"))), Thin, F.Id("y"), Thin, Colon, Thin, Seq(OpenBrace, Seq(F.Id("y"), Thin, Colon, Thin, Seq(Mathbb, Grp(F.Id("R"))), Thin, Seq(Slash,Slash), Thin, F.Id("y"), Thin, InMacro, Thin, F.Id("X"), Thin, Land, Thin, F.Id("y"), Thin, Neq, Thin, F.Id("x")), CloseBrace), Thin, Mapsto, Thin, Seq(Operatorname, Grp(F.Id("Real"))), Thin, Dot, Thin, Seq(Operatorname, Grp(F.Id("rpow"))), Thin, Bar, Thin, Parenthesized(Seq(F.Id("y"), Thin, Colon, Thin, Seq(Mathbb, Grp(F.Id("R"))))), Thin, Minus, Thin, F.Id("x"), Thin, Bar, Thin, Parenthesized(Seq(Minus, Thin, F.Id("s"))))), Thin, Land, Thin, Seq(Operatorname, Grp(F.Id("HasSum"))), Thin, Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("fun"))), Thin, F.Id("y"), Thin, Colon, Thin, Seq(OpenBrace, Seq(F.Id("y"), Thin, Colon, Thin, Seq(Mathbb, Grp(F.Id("R"))), Thin, Seq(Slash,Slash), Thin, F.Id("y"), Thin, InMacro, Thin, F.Id("X"), Thin, Land, Thin, F.Id("y"), Thin, Neq, Thin, F.Id("x")), CloseBrace), Thin, Mapsto, Thin, Seq(Operatorname, Grp(F.Id("Real"))), Thin, Dot, Thin, Seq(Operatorname, Grp(F.Id("sign"))), Thin, Parenthesized(Seq(Parenthesized(Seq(F.Id("y"), Thin, Colon, Thin, Seq(Mathbb, Grp(F.Id("R"))))), Thin, Minus, Thin, F.Id("x"))), Thin, Cdot, Thin, Seq(Operatorname, Grp(F.Id("Real"))), Thin, Dot, Thin, Seq(Operatorname, Grp(F.Id("rpow"))), Thin, Bar, Thin, Parenthesized(Seq(F.Id("y"), Thin, Colon, Thin, Seq(Mathbb, Grp(F.Id("R"))))), Thin, Minus, Thin, F.Id("x"), Thin, Bar, Thin, Parenthesized(Seq(Minus, Thin, F.Id("s"))))), Thin, D(0)))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Definition 1.1 (p. 2): “Let s > 1. An s-equilibrium is a set X ⊂ ℝ with at least two points that is locally finite (every bounded interval contains only finitely many points of X) and satisfies, for every x ∈ X,” the finite-magnitude sum (1) and the zero signed sum (2). The formula states both sums explicitly, indexed by the subtype of points of X distinct from x. Summable and HasSum express unordered convergence."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("arithmetic-progression"),
                DeclarationHandle.Create(Module + ".arithmeticProgression"),
                H("arithmeticProgression"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Thin, Parenthesized(Seq(Alpha, Thin, Beta, Thin, Colon, Thin, Seq(Mathbb, Grp(F.Id("R"))))), Thin, Comma, Thin, Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("arithmeticProgression"))), Thin, Alpha, Thin, Beta, Thin, Eq, Thin, Seq(Operatorname, Grp(F.Id("Set"))), Thin, Dot, Thin, Seq(Operatorname, Grp(F.Id("range"))), Thin, Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("fun"))), Thin, F.Id("n"), Thin, Colon, Thin, Seq(Mathbb, Grp(F.Id("Z"))), Thin, Mapsto, Thin, Alpha, Thin, Cdot, Thin, Parenthesized(Seq(F.Id("n"), Thin, Colon, Thin, Seq(Mathbb, Grp(F.Id("R"))))), Thin, Plus, Thin, Beta))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Theorem 1.2 (p. 2): “Then X = {αn + β : n ∈ ℤ} for some α > 0 and β ∈ ℝ.” The set is the range over all integers; positivity is imposed by the theorems that use it."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("equilibrium-enumeration"),
                DeclarationHandle.Create(Module + ".equilibrium_enumeration"),
                H("equilibrium enumeration"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Thin, Parenthesized(Seq(F.Id("s"), Thin, Colon, Thin, Seq(Mathbb, Grp(F.Id("R"))))), Thin, Comma, Thin, Forall, Thin, Parenthesized(Seq(F.Id("X"), Thin, Colon, Thin, Seq(Operatorname, Grp(F.Id("Set"))), Thin, Seq(Mathbb, Grp(F.Id("R"))))), Thin, Comma, Thin, Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("IsSEquilibrium"))), Thin, F.Id("s"), Thin, F.Id("X"))), Thin, To, Thin, Exists, Thin, F.Id("a"), Thin, Colon, Thin, Seq(Mathbb, Grp(F.Id("Z"))), Thin, To, Thin, Seq(Mathbb, Grp(F.Id("R"))), Thin, Comma, Thin, Seq(Operatorname, Grp(F.Id("StrictMono"))), Thin, F.Id("a"), Thin, Land, Thin, Seq(Operatorname, Grp(F.Id("Set"))), Thin, Dot, Thin, Seq(Operatorname, Grp(F.Id("range"))), Thin, F.Id("a"), Thin, Eq, Thin, F.Id("X")))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Every equilibrium admits a strictly increasing enumeration indexed by all integers. Local finiteness and the exclusion of extremal particles give the two-sided discrete order."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("indexed-force"),
                DeclarationHandle.Create(Module + ".indexedForce"),
                H("indexedForce"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Thin, Parenthesized(Seq(F.Id("s"), Thin, Colon, Thin, Seq(Mathbb, Grp(F.Id("R"))))), Thin, Comma, Thin, Forall, Thin, Parenthesized(Seq(F.Id("a"), Thin, Colon, Thin, Seq(Mathbb, Grp(F.Id("Z"))), Thin, To, Thin, Seq(Mathbb, Grp(F.Id("R"))))), Thin, Comma, Thin, Forall, Thin, Parenthesized(Seq(F.Id("n"), Thin, F.Id("j"), Thin, Colon, Thin, Seq(Mathbb, Grp(F.Id("Z"))))), Thin, Comma, Thin, Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("indexedForce"))), Thin, F.Id("s"), Thin, F.Id("a"), Thin, F.Id("n"), Thin, F.Id("j"), Thin, Eq, Thin, Seq(Operatorname, Grp(F.Id("Real"))), Thin, Dot, Thin, Seq(Operatorname, Grp(F.Id("sign"))), Thin, Parenthesized(Seq(F.Id("a"), Thin, F.Id("j"), Thin, Minus, Thin, F.Id("a"), Thin, F.Id("n"))), Thin, Cdot, Thin, Bar, Thin, F.Id("a"), Thin, F.Id("j"), Thin, Minus, Thin, F.Id("a"), Thin, F.Id("n"), Thin, Bar, Thin, Seq(Caret, Grp(Seq(Minus, Thin, F.Id("s"))))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The signed force at integer index n due to index j. Strictly increasing enumerations identify this expression with the force terms of Definition 1.1. The diagonal value is zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("equilibrium-indexed-force"),
                DeclarationHandle.Create(Module + ".equilibrium_indexed_force"),
                H("equilibrium indexed force"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Thin, Parenthesized(Seq(F.Id("s"), Thin, Colon, Thin, Seq(Mathbb, Grp(F.Id("R"))))), Thin, Comma, Thin, Forall, Thin, Parenthesized(Seq(F.Id("X"), Thin, Colon, Thin, Seq(Operatorname, Grp(F.Id("Set"))), Thin, Seq(Mathbb, Grp(F.Id("R"))))), Thin, Comma, Thin, Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("IsSEquilibrium"))), Thin, F.Id("s"), Thin, F.Id("X"))), Thin, To, Thin, Forall, Thin, Parenthesized(Seq(F.Id("a"), Thin, Colon, Thin, Seq(Mathbb, Grp(F.Id("Z"))), Thin, To, Thin, Seq(Mathbb, Grp(F.Id("R"))))), Thin, Comma, Thin, Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("StrictMono"))), Thin, F.Id("a"))), Thin, To, Thin, Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("Set"))), Thin, Dot, Thin, Seq(Operatorname, Grp(F.Id("range"))), Thin, F.Id("a"), Thin, Eq, Thin, F.Id("X"))), Thin, To, Thin, Forall, Thin, F.Id("n"), Thin, Colon, Thin, Seq(Mathbb, Grp(F.Id("Z"))), Thin, Comma, Thin, Seq(Operatorname, Grp(F.Id("HasSum"))), Thin, Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("indexedForce"))), Thin, F.Id("s"), Thin, F.Id("a"), Thin, F.Id("n"))), Thin, D(0)))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Transport along the increasing enumeration preserves the zero signed force sum, with the diagonal term equal to zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("equilibrium-indexed-total"),
                DeclarationHandle.Create(Module + ".equilibrium_indexed_total"),
                H("equilibrium indexed total"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Thin, Parenthesized(Seq(F.Id("s"), Thin, Colon, Thin, Seq(Mathbb, Grp(F.Id("R"))))), Thin, Comma, Thin, Forall, Thin, Parenthesized(Seq(F.Id("X"), Thin, Colon, Thin, Seq(Operatorname, Grp(F.Id("Set"))), Thin, Seq(Mathbb, Grp(F.Id("R"))))), Thin, Comma, Thin, Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("IsSEquilibrium"))), Thin, F.Id("s"), Thin, F.Id("X"))), Thin, To, Thin, Forall, Thin, Parenthesized(Seq(F.Id("a"), Thin, Colon, Thin, Seq(Mathbb, Grp(F.Id("Z"))), Thin, To, Thin, Seq(Mathbb, Grp(F.Id("R"))))), Thin, Comma, Thin, Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("StrictMono"))), Thin, F.Id("a"))), Thin, To, Thin, Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("Set"))), Thin, Dot, Thin, Seq(Operatorname, Grp(F.Id("range"))), Thin, F.Id("a"), Thin, Eq, Thin, F.Id("X"))), Thin, To, Thin, Forall, Thin, F.Id("n"), Thin, Colon, Thin, Seq(Mathbb, Grp(F.Id("Z"))), Thin, Comma, Thin, Seq(Operatorname, Grp(F.Id("Summable"))), Thin, Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("fun"))), Thin, F.Id("j"), Thin, Colon, Thin, Seq(Mathbb, Grp(F.Id("Z"))), Thin, Mapsto, Thin, Bar, Thin, F.Id("a"), Thin, F.Id("j"), Thin, Minus, Thin, F.Id("a"), Thin, F.Id("n"), Thin, Bar, Thin, Seq(Caret, Grp(Seq(Minus, Thin, F.Id("s"))))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Transport along the increasing enumeration preserves absolute summability of the inverse-power forces, with the diagonal term equal to zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("constant-gap-affine"),
                DeclarationHandle.Create(Module + ".constant_gap_affine"),
                H("constant gap affine"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Thin, Parenthesized(Seq(F.Id("a"), Thin, Colon, Thin, Seq(Mathbb, Grp(F.Id("Z"))), Thin, To, Thin, Seq(Mathbb, Grp(F.Id("R"))))), Thin, Comma, Thin, Forall, Thin, Parenthesized(Seq(Alpha, Thin, Colon, Thin, Seq(Mathbb, Grp(F.Id("R"))))), Thin, Comma, Thin, Parenthesized(Seq(Forall, Thin, F.Id("n"), Thin, Colon, Thin, Seq(Mathbb, Grp(F.Id("Z"))), Thin, Comma, Thin, F.Id("a"), Thin, Parenthesized(Seq(F.Id("n"), Thin, Plus, Thin, D(1))), Thin, Minus, Thin, F.Id("a"), Thin, F.Id("n"), Thin, Eq, Thin, Alpha)), Thin, To, Thin, Forall, Thin, F.Id("n"), Thin, Colon, Thin, Seq(Mathbb, Grp(F.Id("Z"))), Thin, Comma, Thin, F.Id("a"), Thin, F.Id("n"), Thin, Eq, Thin, Alpha, Thin, Cdot, Thin, Parenthesized(Seq(F.Id("n"), Thin, Colon, Thin, Seq(Mathbb, Grp(F.Id("R"))))), Thin, Plus, Thin, F.Id("a"), Thin, D(0)))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("A sequence with constant consecutive difference is affine on all integers."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("progression-equilibrium"),
                DeclarationHandle.Create(Module + ".progression_equilibrium"),
                H("progression equilibrium"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Thin, Parenthesized(Seq(F.Id("s"), Thin, Alpha, Thin, Beta, Thin, Colon, Thin, Seq(Mathbb, Grp(F.Id("R"))))), Thin, Comma, Thin, Parenthesized(Seq(D(1), Thin, Lt, Thin, F.Id("s"))), Thin, To, Thin, Parenthesized(Seq(D(0), Thin, Lt, Thin, Alpha)), Thin, To, Thin, Seq(Operatorname, Grp(F.Id("IsSEquilibrium"))), Thin, F.Id("s"), Thin, Parenthesized(Seq(Seq(Operatorname, Grp(F.Id("arithmeticProgression"))), Thin, Alpha, Thin, Beta))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Every affine integer progression with positive scale is an equilibrium for every real exponent greater than one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("equilibrium-exists"),
                DeclarationHandle.Create(Module + ".equilibrium_exists"),
                H("equilibrium exists"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Thin, Parenthesized(Seq(F.Id("s"), Thin, Colon, Thin, Seq(Mathbb, Grp(F.Id("R"))))), Thin, Comma, Thin, Parenthesized(Seq(D(1), Thin, Lt, Thin, F.Id("s"))), Thin, To, Thin, Exists, Thin, F.Id("X"), Thin, Colon, Thin, Seq(Operatorname, Grp(F.Id("Set"))), Thin, Seq(Mathbb, Grp(F.Id("R"))), Thin, Comma, Thin, Seq(Operatorname, Grp(F.Id("IsSEquilibrium"))), Thin, F.Id("s"), Thin, F.Id("X")))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every real exponent greater than one, the integer lattice supplies an equilibrium."))),
                DescribeRole.Theorem))));

    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
}
