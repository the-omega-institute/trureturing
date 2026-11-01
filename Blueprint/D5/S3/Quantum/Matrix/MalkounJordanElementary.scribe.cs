using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class MalkounJordanElementaryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/MalkounJordanElementary.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/malkoun2026mo512579");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Elementary symmetric eigenvalue inequality for a Hermitian Jordan product.",
        H("Malkoun's two-matrix elementary symmetric inequality"),
        Blocks(
            Node("elementarySymmetric", "The elementary symmetric polynomial",
                "The kth elementary symmetric polynomial is the sum of products over all k-element subsets of Fin n. "
                + "The entries are real; repeated values occupy distinct indices and retain their multiplicity.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The complete source assertion",
                "MathOverflow 512579, revision 1, displayed first question (unpaginated): for every positive n, "
                + "every pair of complex n-by-n Hermitian positive semidefinite matrices X,Y, and every 1 ≤ k ≤ n, "
                + "the kth elementary symmetric polynomial of the eigenvalues of XY+YX is at most that of X²+Y². "
                + "Matrix.IsHermitian.eigenvalues lists the real eigenvalues with algebraic multiplicity, as certified by "
                + "Mathlib's roots_charpoly_eq_eigenvalues. The positivity hypotheses concern X and Y. "
                + "No positivity, invertibility, rank, simplicity of spectrum or small-order condition is imposed on XY+YX. "
                + "The unspecified subsequent promotion question is outside this assertion.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The elementary symmetric inequality",
                "Fix a principal column set S. Stack the selected columns of X above those of Y to obtain U, "
                + "and reverse the two blocks to obtain V. Hermiticity gives U*U=V*V=(X²+Y²)[S,S] "
                + "and U*V=(XY+YX)[S,S]. The public frozen cauchyBinet declaration expands each determinant "
                + "over the same ordered row subsets. Writing u and v for the resulting minor determinants, "
                + "the real part of conjugate(u)v is at most half the sum of their squared moduli. "
                + "Summing and using the equal Gram matrices proves the inequality of the real principal determinants. "
                + "The characteristic-polynomial principal-minor identity and Hermitian spectral factorization identify "
                + "the sum of these determinants with the original elementary symmetric polynomial. "
                + "Summing the principal-minor inequalities proves the complete source assertion. "
                + "All determinant identities are polynomial, so zero and singular matrices remain in scope. "
                + "This is an application of existing Cauchy–Binet and spectral identities; no worldwide priority is asserted.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("malkoun-jordan-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Presentation(name)),
            provenance, Blocks(Paragraph(Text(prose))), role,
            openProblemResolutionClaim: name == "result"
                ? new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("malkoun-2026-mo512579-jordan-elementary"),
                    ResolutionKind.Proved)
                : null);

    private static Formula I(string name) => F.Id(name);
    private static Formula Part(string name)
    {
        var parts = name.Split('_');
        Formula value = I(parts[^1]);
        for (var index = parts.Length - 2; index >= 0; --index)
            value = Seq(I(parts[index]), Underscore, Grp(value));
        return value;
    }
    private static Formula Name(string name)
    {
        if (!name.Contains('.')) return Part(name);
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(Part(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula App(string name, params Formula[] args) => new Formula.Apply(Name(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Seq(I(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Imp(Formula premise, Formula body) =>
        new Formula.Logic(Par(premise), FormulaLogicOperator.Implies, Par(body));
    private static Formula LE(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula LT(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Nat => Seq(Mathbb, Grp(I("N")));
    private static Formula Herm(string h) => App("Matrix.PosSemidef.isHermitian", I(h));
    private static Formula E(Formula h) => App("elementarySymmetric", App("Matrix.IsHermitian.eigenvalues", h), I("k"));
    private static Formula Body()
    {
        var n = I("n"); var x = I("X"); var y = I("Y"); var k = I("k");
        var matrix = App("Matrix", App("Fin", n), App("Fin", n), Seq(Mathbb, Grp(I("C"))));
        var left = E(App("jordan_hermitian", Herm("hX"), Herm("hY")));
        var right = E(App("Matrix.IsHermitian.add", App("Matrix.IsHermitian.pow", Herm("hX"), D(2)), App("Matrix.IsHermitian.pow", Herm("hY"), D(2))));
        return All("n", Nat, Imp(LT(D(0), n), All("X", matrix, All("Y", matrix,
            All("hX", App("Matrix.PosSemidef", x), All("hY", App("Matrix.PosSemidef", y),
            All("k", Nat, Imp(LE(D(1), k), Imp(LE(k, n), LE(left, right))))))))));
    }
    private static Formula Presentation(string name) => name switch
    {
        "claim" => Disp(Equal(I("claim"), Par(Body()))),
        "result" => Disp(I("claim")),
        _ => Disp(All("n", Nat,
            All("t", new Formula.TypeArrow(App("Fin", I("n")), Seq(Mathbb, Grp(I("R")))),
            All("k", Nat, Equal(App("elementarySymmetric", I("t"), I("k")),
                Seq(Sum, Underscore, Grp(Seq(I("S"), InMacro, Sp,
                        App("Finset.powersetCard", I("k"),
                            Par(Seq(Name("Finset.univ"), Colon, Sp, App("Finset", App("Fin", I("n")))))))),
                    Prod, Underscore, Grp(Seq(I("i"), InMacro, Sp, I("S"))), App("t", I("i"))))))))
    };
}
