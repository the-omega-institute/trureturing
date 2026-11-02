using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class OEISA189733DenominatorConjectureDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Residue/OEISA189733DenominatorConjecture.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/curtz2011a189733");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The reduced denominators of Curtz's rational triangle satisfy all six residue formulas.",
        H("Curtz's OEIS A189733 denominator conjecture"),
        Blocks(
            Paragraph(Text("All indices are natural numbers and all triangle values are rational. "
                + "Write T for triangle and let den be the reduced rational denominator, "
                + "including den(0)=1. The upper-triangular source array is reindexed by "
                + "T(m,k)=B(m,m+k). Boundary cases take precedence over the recurrence. "
                + "The lower-triangular extension is not used.")),
            Node("triangle", "The literal rational triangle", TriangleFormula(),
                "The three branches uniquely define the array by induction on the second index. "
                + "In the source first-superdiagonal formula the exponent is m+2, giving the "
                + "same sign as m. No closed form is assumed.", DescribeRole.Definition, true),
            Node("a", "The denominator sequence", AFormula(),
                "This is the actual reduced denominator of the zeroth-row entry, "
                + "not the denominator of an unreduced expression.", DescribeRole.Definition, true),
            Node("result", "The six universal denominator formulas", ResultFormula(),
                "The assertion includes k=0 and has no additional hypotheses. "
                + "Finite polynomial moments connect the source recursion to the companion "
                + "polynomials. The derivative identity gives an endpoint difference, "
                + "and the recurrence at X=1 supplies period six. Positive reciprocal "
                + "denominators then give the displayed reduced values.", DescribeRole.Theorem,
                resolution: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a189733-curtz-denominator-conjecture"),
                    ResolutionKind.Proved)),
            Paragraph(Text("For the algebraic argument, define rational polynomials Q and L "
                + "and a finite coefficient moment J as follows. The sum ranges over the "
                + "finite support of P; X is the polynomial variable.")),
            new DocumentBlock.DisplayFormula(BridgeDefinitions()),
            Paragraph(Text("Multiplication by X shifts the moment index from m to m+1. "
                + "Induction on the source recursion proves the first identity below. "
                + "The companion relation proves the derivative identity by induction. "
                + "On each monomial, J(0,P') equals the difference of its endpoint values, "
                + "so linearity gives the last identity.")),
            new DocumentBlock.DisplayFormula(BridgeIdentities()),
            Paragraph(Text("At X=1, the companion recurrence has initial values two and one "
                + "and repeats after six steps. Its six consecutive values are "
                + "2, 1, -1, -2, -1, 1. Substitution in the endpoint identity yields the "
                + "following exact rational values for every k.")),
            new DocumentBlock.DisplayFormula(RowFormula()),
            Paragraph(Text("The source and exact assertion are also recorded at "
                + "https://github.com/the-omega-institute/trureturing/issues/25342. "
                + "The conclusion concerns the six formulas in OEIS A189733; it makes "
                + "no claim of exhaustive literature coverage or worldwide priority.")))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, bool literature = false,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("a189733-" + name), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source)
                : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula All(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), Nat(), body);
    private static Formula P(Formula value) => Seq(Open, value, Close);
    private static Formula Div(Formula a, Formula b) => Seq(P(a), Sp, Slash, Sp, P(b));
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(P(a), b);
    private static Formula Neg(Formula value) => new Formula.Negate(value);
    private static Formula Tuple(params Formula[] values)
    {
        var parts = new System.Collections.Generic.List<Formula> { Open };
        for (int i = 0; i < values.Length; ++i)
        {
            if (i != 0) { parts.Add(Comma); parts.Add(Sp); }
            parts.Add(values[i]);
        }
        parts.Add(Close);
        return Seq([.. parts]);
    }

    private static Formula TriangleFormula()
    {
        Formula m = F.Id("m"), k = F.Id("k");
        return All("m", new Formula.Aligned([
            Equal(Call("T", m, D(0)), D(0)),
            Equal(Call("T", m, D(1)), Div(Pow(Neg(D(1)), m), Add(m, D(1)))),
            All("k", Equal(Call("T", m, Add(k, D(2))),
                Add(Call("T", m, Add(k, D(1))), Call("T", Add(m, D(1)), k))))
        ]));
    }

    private static Formula AFormula() => All("n",
        Equal(Call("a", F.Id("n")), Call("den", Call("T", D(0), F.Id("n")))));

    private static Formula[] Indices()
    {
        Formula b = Multiply(D(6), F.Id("k"));
        return [b, Add(b, D(1)), Add(b, D(2)), Add(b, D(3)), Add(b, D(4)), Add(b, D(5))];
    }

    private static Formula ResultFormula()
    {
        Formula k = F.Id("k");
        Formula[] lhs = System.Array.ConvertAll(Indices(), n => Call("a", n));
        return All("k", Equal(Tuple(lhs), Tuple(D(1), Add(Multiply(D(3), k), D(1)),
            Add(Multiply(D(2), k), D(1)), Add(Multiply(D(3), k), D(2)), D(1),
            Add(Multiply(D(6), k), D(6)))));
    }

    private static Formula BridgeDefinitions()
    {
        Formula n = F.Id("n"), m = F.Id("m"), p = F.Id("P"), i = F.Id("i");
        return new Formula.Aligned([
            Equal(Tuple(Call("Q", D(0)), Call("Q", D(1))), Tuple(D(0), D(1))),
            Equal(Tuple(Call("L", D(0)), Call("L", D(1))), Tuple(D(2), D(1))),
            Equal(Call("Q", Add(n, D(2))), Subtract(Call("Q", Add(n, D(1))),
                Multiply(F.Id("X"), Call("Q", n)))),
            Equal(Call("L", Add(n, D(2))), Subtract(Call("L", Add(n, D(1))),
                Multiply(F.Id("X"), Call("L", n)))),
            Equal(Call("J", m, p), Seq(
                new Formula.Subscript(Sum, Seq(i, InMacro, Call("support", p))),
                Div(Call("coeff", p, i), Add(Add(m, i), D(1)))))
        ]);
    }

    private static Formula BridgeIdentities()
    {
        Formula n = F.Id("n"), m = F.Id("m");
        return new Formula.Aligned([
            Equal(Call("T", m, n), Multiply(Pow(Neg(D(1)), m), Call("J", m, Call("Q", n)))),
            Equal(Call("L", Add(n, D(1))), Subtract(Call("Q", Add(n, D(1))),
                Multiply(Multiply(D(2), F.Id("X")), Call("Q", n)))),
            Equal(Call("derivative", Call("L", Add(n, D(1)))),
                Multiply(Neg(P(Add(n, D(1)))), Call("Q", n))),
            Equal(Call("T", D(0), n), Div(Subtract(D(1),
                Call("eval", Call("L", Add(n, D(1))), D(1))), Add(n, D(1))))
        ]);
    }

    private static Formula RowFormula()
    {
        Formula k = F.Id("k");
        return All("k", Equal(Tuple(System.Array.ConvertAll(Indices(), n => Call("T", D(0), n))),
            Tuple(D(0), Div(D(1), Add(Multiply(D(3), k), D(1))),
                Div(D(1), Add(Multiply(D(2), k), D(1))),
                Div(D(1), Add(Multiply(D(3), k), D(2))), D(0),
                Neg(Div(D(1), Add(Multiply(D(6), k), D(6)))))));
    }
}
