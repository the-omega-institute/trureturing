using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements;

internal sealed class UnitaryOrthogonalWeightDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unitary invariance and orthogonal additivity determine nonnegative vector weights.",
        H("Unitary invariant orthogonal weights"),
        Blocks(Describe.Lean(
            DescribeId.Create("unitary-orthogonal-weight-equals-squared-norm"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/Measurements/UnitaryOrthogonalWeight.unitary_orthogonal_weight_eq_norm_sq"),
            H("Uniqueness of the squared norm"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let H be a complete inner-product space over the real or complex "
                    + "numbers, of cardinal dimension at least two. The weight takes values in "
                    + "the nonnegative reals, with no upper bound and no regularity assumption.")),
                Paragraph(Text("Every two vectors of equal norm are related by a linear isometric "
                    + "equivalence. To construct it, extend the singleton-span isometry inside the "
                    + "finite-dimensional span of the two vectors, then act identically on its "
                    + "orthogonal complement. This applies also when H is infinite-dimensional.")),
                Paragraph(Text("Two orthonormal directions give an additive function f on "
                    + "nonnegative squared radii. Nonnegativity makes f monotone. Normalization "
                    + "gives f(1)=1, additivity fixes every nonnegative rational, and rational "
                    + "density then fixes every nonnegative real. Equal-norm transport gives "
                    + "the asserted identity for every vector."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) content.Add(Comma);
            content.Add(args[i]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula App(Formula f, Formula x) => Seq(f, Open, x, Close);
    private static Formula Typed(Formula x, Formula t) => Seq(x, Colon, Sp, t);
    private static Formula Statement()
    {
        Formula k = F.Id("K"), h = F.Id("H"), w = F.Id("W");
        Formula u = F.Id("u"), v = F.Id("v"), x = F.Id("x"), y = F.Id("y");
        Formula isometry = F.Id("U");
        Formula norm(Formula z) => new Formula.Norm(z);
        Formula square(Formula z) => Seq(z, Caret, Grp(D(2)));
        Formula nonnegativeReals = Seq(Mathbb, Grp(F.Id("R")), Underscore, Grp(Seq(Geq, D(0))));
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(k, Call("Type")), Comma, Sp, Typed(h, Call("Type")), Comma,
            RowBreak, Grp(),
            OpenBracket, Call("RCLike", k), CloseBracket, Comma, Sp,
            OpenBracket, Call("NormedAddCommGroup", h), CloseBracket, Comma, Sp,
            OpenBracket, Call("InnerProductSpace", k, h), CloseBracket, Comma, Sp,
            OpenBracket, Call("CompleteSpace", h), CloseBracket, Comma,
            RowBreak, Grp(),
            D(2), Leq, Sp, Call("rank", k, h), Comma, Sp,
            Typed(w, Seq(h, To, Sp, nonnegativeReals)), Comma,
            RowBreak, Grp(),
            OpenBracket, Forall, Sp, Typed(isometry, Call("LinearIsometryEquiv", k, h, h)),
            Comma, Sp, Typed(v, h), Comma, Sp,
            App(w, App(isometry, v)), Eq, Sp, App(w, v), CloseBracket, Comma,
            RowBreak, Grp(),
            OpenBracket, Forall, Sp, Typed(x, h), Comma, Sp, Typed(y, h), Comma, Sp,
            Call("inner", k, x, y), Eq, D(0), Rightarrow, Sp,
            App(w, Seq(x, Plus, y)), Eq, Sp, App(w, x), Plus, App(w, y), CloseBracket, Comma,
            RowBreak, Grp(),
            OpenBracket, Forall, Sp, Typed(u, h), Comma, Sp,
            norm(u), Eq, D(1), Rightarrow, Sp, App(w, u), Eq, D(1), CloseBracket,
            RowBreak, Grp(),
            Rightarrow, Sp, Forall, Sp, Typed(v, h), Comma, Sp,
            Call("coe", App(w, v)), Eq, Sp, square(norm(v)), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
