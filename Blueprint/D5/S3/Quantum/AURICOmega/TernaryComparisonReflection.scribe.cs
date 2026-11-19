using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.AURICOmega;

internal sealed class TernaryComparisonReflectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/AURICOmega/TernaryComparisonReflection.";
    private static LibraryNoteRef Heap => LibraryNoteRef.Create("D5/L/Semigroups/certaine1943ternary");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two-point reflection sequences are group powers, so equally spaced readings agree.",
        H("Reflection sequences of ternary comparison structures"),
        Blocks(
            Node("reflection-seq", "reflectionSeq", "The reflection sequence through two points",
                StatementSource.FromAuthor(ReflectionSeqFormula()), AssessedProvenance.FromRepo(),
                "For points a and b of a ternary comparison structure C, the reflection sequence x starts with x 0 = a and x 1 = b, "
                    + "and each further point x (n + 2) = tri (x (n + 1)) (x n) (x (n + 1)) is the reflection of the point before last through the last point. "
                    + "In a group with the transfer x * y^-1 * z this is the step x (n + 2) = x (n + 1) * (x n)^-1 * x (n + 1).",
                DescribeRole.Definition),
            Node("eq-pow", "reflectionSeq_eq_pow", "Reflection sequences are powers",
                StatementSource.FromAuthor(EqPowFormula()), AssessedProvenance.FromRepo(Heap),
                "In the group at a, where a is the identity and tri x y z = x * y^-1 * z, the n-th point of the reflection sequence is b^n. "
                    + "The proof is an induction on pairs of consecutive points: x 0 = a = b^0 and x 1 = b = b^1, and if x n = b^n and x (n + 1) = b^(n + 1), "
                    + "then x (n + 2) = b^(n + 1) * (b^n)^-1 * b^(n + 1) = b^(n + 2). "
                    + "Thus the sequence consists of the powers of b in the group at a.",
                DescribeRole.Theorem),
            Node("kappa-add", "kappa_reflectionSeq_add", "Equally spaced readings agree",
                StatementSource.FromAuthor(KappaAddFormula()), AssessedProvenance.FromRepo(),
                "For all natural numbers m and n, the reading between the m-th and the (m + n)-th point of the reflection sequence equals the reading between the starting point a and the n-th point. "
                    + "By the previous theorem the two points are b^m and b^m * b^n in the group at a. "
                    + "Left multiplication by b^m in that group is the transfer y -> tri (b^m) a y, under which the reading is invariant, "
                    + "and tri (b^m) a a = b^m, so the reading of b^m and b^m * b^n equals the reading of a and b^n.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(
        string id, string selector, string title, StatementSource statement,
        AssessedProvenance provenance, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("ternary-comparison-reflection-" + id),
            DeclarationHandle.Create(Prefix + selector), H(title), statement, provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Rel(Formula x, FormulaRelationOperator op, Formula y) => new Formula.Relation(x, op, y);
    private static Formula Equal(Formula x, Formula y) => Rel(x, FormulaRelationOperator.Equal, y);
    private static Formula Logic(Formula x, FormulaLogicOperator op, Formula y) => new Formula.Logic(x, op, y);
    private static Formula And(Formula x, Formula y) => Logic(x, FormulaLogicOperator.And, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula ForAllMany(Formula domain, Formula body, params string[] names) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [.. names.Select(name => new Formula.BoundVariable(FormulaIdentifier.Create(name), domain))], body);

    private static Formula M => F.Id("M");
    private static Formula C => F.Id("C");
    private static Formula A => F.Id("a");
    private static Formula B => F.Id("b");
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula TypeStar => Seq(Operatorname, Grp(F.Id("Type")), Star);

    /// <summary>Closes a body over the carrier M, the structure C and the two points a and b.</summary>
    private static Formula OverPoints(Formula body) =>
        Disp(ForAll("M", TypeStar, ForAll("C", Call("TernaryComparison", M), ForAllMany(M, body, "a", "b"))));

    private static Formula X(Formula index) => Call("reflectionSeq", C, A, B, index);
    private static Formula Tri(Formula x, Formula y, Formula z) => Call("tri", C, x, y, z);
    private static Formula Kappa(Formula x, Formula y) => Call("kappa", C, x, y);

    private static Formula ReflectionSeqFormula()
    {
        Formula n = F.Id("n");
        Formula step = Equal(X(Add(n, D(2))), Tri(X(Add(n, D(1))), X(n), X(Add(n, D(1)))));
        return OverPoints(And(Equal(X(D(0)), A),
            And(Equal(X(D(1)), B), ForAll("n", Naturals, step))));
    }

    private static Formula EqPowFormula()
    {
        Formula n = F.Id("n");
        return OverPoints(ForAll("n", Naturals,
            Equal(X(n), Call("pow", Call("groupAt", C, A), B, n))));
    }

    private static Formula KappaAddFormula()
    {
        Formula m = F.Id("m"), n = F.Id("n");
        return OverPoints(ForAllMany(Naturals,
            Equal(Kappa(X(m), X(Add(m, n))), Kappa(A, X(n))), "m", "n"));
    }
}
