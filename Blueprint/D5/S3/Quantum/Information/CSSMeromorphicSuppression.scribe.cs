using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class CSSMeromorphicSuppressionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/CSSMeromorphicSuppression.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/burton2026meromorphic");

    private const string CodewordDerivation =
        "For ψ_z = (1, z), |0_L⟩ ∝ ∑_{g ∈ G_X} |g⟩ and |1_L⟩ = X^{⊗n}|0_L⟩. " +
        "Up to the common normalization, the denominator is ⟨0_L|ψ_z^{⊗n}⟩ = ∑_{g ∈ G_X} z^{wt(g)} " +
        "and the numerator is ⟨1_L|ψ_z^{⊗n}⟩ = ∑_{g ∈ G_X} z^{wt(g + one)}. " +
        "This is the codeword derivation of Theorem 4.4 and Appendix B of arXiv:2605.06251v1. ";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every CSS code with logical X and Z strings has coherent error suppression of order at least its distance at 0, infinity, 1 and -1.",
        H("Burton--Anwar CSS meromorphic suppression"),
        Blocks(
            Node("wt", "Binary Hamming weight", WtFormula(),
                "For a binary vector x on Fin(n), wt is the cardinality of the coordinates where x is nonzero.",
                "wt", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("one", "The all-ones vector", OneFormula(),
                "The vector one has value 1 at every coordinate of Fin(n).",
                "one", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("code", "CSS code data", CssCodeFormula(),
                "A CSSCode n consists of the two displayed Submodule fields GX and GZ. The seven constraints, in order, are commutation, evenX, evenZ, one_not_X, one_not_Z, odd_length and one_qubit.",
                "CSSCode", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("logical", "Logical Pauli representatives", IsLogicalFormula(),
                "IsLogical requires each Pauli component to commute with the opposite stabilizer and excludes the pair in which both components are stabilizers.",
                "IsLogical", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("weight", "Pauli weight", PauliWeightFormula(),
                "The Pauli weight counts coordinates where either the X or Z component is nonzero.",
                "pauliWeight", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("distance", "Code distance", HasDistanceFormula(),
                "HasDistance records a logical Pauli of weight d and the universal lower bound d for every logical Pauli.",
                "HasDistance", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("den", "Decoder denominator", DecoderDenFormula(),
                CodewordDerivation + "The polynomial decoderDen records the denominator amplitude.",
                "decoderDen", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("num", "Decoder numerator", DecoderNumFormula(),
                CodewordDerivation + "The polynomial decoderNum records the numerator amplitude.",
                "decoderNum", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("order", "Finite suppression order", SuppressionOrderFormula(),
                "At a finite point a, suppressionOrder is the root multiplicity of the numerator minus a times the denominator.",
                "suppressionOrder", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("order-inf", "Suppression order at infinity", SuppressionOrderInfFormula(),
                "At infinity, suppressionOrderInf is the root multiplicity at zero of the degree-n reversed denominator.",
                "suppressionOrderInf", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("fix", "Finite fixed point with order", FixesWithFormula(),
                "FixesWith says that the denominator is nonzero and the decoder numerator equals a times the denominator at a.",
                "FixesWith", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("fix-inf", "The fixed point at infinity", FixesWithInfFormula(),
                "FixesWithInf is the nonvanishing of the reversed numerator at zero.",
                "FixesWithInf", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 4.8", ClaimFormula(),
                "Conjecture 4.8 (Burton and Anwar, arXiv:2605.06251v1, Section 4, p. 14): \"Any CSS code [[n,1,d]] with logical operators X^{⊗n}, Z^{⊗n} exhibits coherent error suppression O(ε^d) at the four stabilizer states z = 0, ∞, ±1.\" The encoding uses the binary CSS conventions above and states the lower bound on local degree.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The four-point suppression theorem", Disp(F.Id("claim")),
                CodewordDerivation + "Adding the all-ones vector sends every X stabilizer to a logical-X representative, so the numerator is divisible by z^d and the denominator is 1 at zero. Degree-n reversal gives infinity. At 1 and -1, binary character orthogonality factors P-Q and P+Q through odd logical-Z representatives, giving the same distance divisibility and the fixed-point equalities.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                null)),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("burton-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name)
    {
        var parts = name.Split('.');
        var tokens = new List<Formula>();
        for (var i = 0; i < parts.Length; i++)
        {
            if (i > 0) tokens.Add(Dot);
            tokens.Add(F.Id(parts[i]));
        }
        return Seq(Operatorname, Grp([.. tokens]));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Ne(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Mem(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Pow(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);
    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Bits() => Call("ZMod", D(2));
    private static Formula Vec(Formula n) => Parenthesized(Seq(Call("Fin", n), To, Bits()));
    private static Formula DotProduct(Formula x, Formula y) => Call("dotProduct", x, y);
    private static Formula Card(Formula s) => Call("Finset.card", s);
    private static Formula Filter(Formula i, Formula type, Formula predicate) =>
        Call("Finset.filter", Fun(i, type, predicate), Parenthesized(Seq(Named("Finset.univ"), Colon, Sp, Call("Finset", type))));
    private static Formula Fun(Formula variable, Formula type, Formula body) =>
        Seq(Named("fun"), Sp, Parenthesized(Seq(variable, Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula SumOver(Formula variable, Formula domain, Formula body) =>
        Seq(Sum, Underscore, Grp(Seq(variable, InMacro, Sp, domain)), Sp, Parenthesized(body));
    private static Formula RootMultiplicity(Formula p, Formula a) =>
        Call("Polynomial.rootMultiplicity", a, p);
    private static Formula StabilizerWords(Formula n, Formula C) =>
        Filter(F.Id("g"), Vec(n), Mem(F.Id("g"), Field(C, "GX")));
    private static Formula Field(Formula C, string field) => Seq(C, Dot, Named(field));
    private static Formula SetList(params Formula[] values) =>
        Seq(OpenBrace, Seq(values.SelectMany((v, i) => i == 0 ? new[] { v } : new Formula[] { Comma, Sp, v }).ToArray()), CloseBrace);

    private static Formula WtFormula()
    {
        Formula n = F.Id("n"), x = F.Id("x"), i = F.Id("i");
        Formula nz = Ne(At(x, i), D(0));
        return Disp(All("n", Nats(), All("x", Vec(n),
            Eq(Call("wt", x), Card(Filter(i, Call("Fin", n), nz))))));
    }

    private static Formula OneFormula()
    {
        Formula n = F.Id("n"), i = F.Id("i");
        return Disp(All("n", Nats(), All("i", Call("Fin", n), Eq(Call("one", i), D(1)))));
    }

    private static Formula CssCodeFormula()
    {
        Formula n = F.Id("n"), GX = F.Id("GX"), GZ = F.Id("GZ"), x = F.Id("x"), z = F.Id("z");
        Formula submodule = Call("Submodule", Bits(), Vec(n));
        Formula commutation = All("x", Vec(n), Imp(Mem(x, GX),
            All("z", Vec(n), Imp(Mem(z, GZ), Eq(DotProduct(x, z), D(0))))));
        Formula evenX = All("x", Vec(n), Imp(Mem(x, GX), Eq(DotProduct(x, Named("one")), D(0))));
        Formula evenZ = All("z", Vec(n), Imp(Mem(z, GZ), Eq(DotProduct(z, Named("one")), D(0))));
        Formula oneNotX = new Formula.Not(Parenthesized(Mem(Named("one"), GX)));
        Formula oneNotZ = new Formula.Not(Parenthesized(Mem(Named("one"), GZ)));
        Formula oddLength = Call("Odd", n);
        Formula oneQubit = Eq(Add(Add(Call("Module.finrank", Bits(), GX),
            Call("Module.finrank", Bits(), GZ)), D(1)), n);
        Formula hypotheses = And(commutation, And(evenX, And(evenZ, And(oneNotX,
            And(oneNotZ, And(oddLength, oneQubit))))));
        Formula fields = Seq(OpenBrace, GX, Colon, Sp, submodule, Semi, Sp,
            GZ, Colon, Sp, submodule, Sp, Mid, Sp, hypotheses, CloseBrace);
        return Disp(All("n", Nats(), Seq(Call("CSSCode", n), Colon, F.Eq, Sp, fields)));
    }

    private static Formula IsLogicalFormula()
    {
        Formula n = F.Id("n"), C = F.Id("C"), x = F.Id("x"), z = F.Id("z"), s = F.Id("s");
        Formula xComm = All("s", Vec(n), Imp(Mem(s, Field(C, "GZ")), Eq(DotProduct(x, s), D(0))));
        Formula zComm = All("s", Vec(n), Imp(Mem(s, Field(C, "GX")), Eq(DotProduct(z, s), D(0))));
        Formula noStab = new Formula.Logic(Parenthesized(Mem(x, Field(C, "GX"))), FormulaLogicOperator.And,
            Parenthesized(Mem(z, Field(C, "GZ"))));
        return Disp(All("n", Nats(), All("C", Call("CSSCode", n), All("x", Vec(n), All("z", Vec(n),
            Eq(Call("IsLogical", C, x, z), And(xComm, And(zComm, new Formula.Not(Parenthesized(noStab))))))))));
    }

    private static Formula PauliWeightFormula()
    {
        Formula n = F.Id("n"), x = F.Id("x"), z = F.Id("z"), i = F.Id("i");
        Formula predicate = Or(Ne(At(x, i), D(0)), Ne(At(z, i), D(0)));
        return Disp(All("n", Nats(), All("x", Vec(n), All("z", Vec(n),
            Eq(Call("pauliWeight", x, z), Card(Filter(i, Call("Fin", n), predicate)))))));
    }

    private static Formula HasDistanceFormula()
    {
        Formula n = F.Id("n"), d = F.Id("d"), C = F.Id("C"), x = F.Id("x"), z = F.Id("z");
        Formula witness = Some("x", Vec(n), Some("z", Vec(n),
            And(Call("IsLogical", C, x, z), Eq(Call("pauliWeight", x, z), d))));
        Formula lower = All("x", Vec(n), All("z", Vec(n),
            Imp(Call("IsLogical", C, x, z), Le(d, Call("pauliWeight", x, z)))));
        return Disp(All("n", Nats(), All("d", Nats(), All("C", Call("CSSCode", n),
            Eq(Call("HasDistance", C, d), And(witness, lower))))));
    }

    private static Formula DecoderDenFormula()
    {
        Formula n = F.Id("n"), C = F.Id("C"), g = F.Id("g");
        return Disp(All("n", Nats(), All("C", Call("CSSCode", n),
            Eq(Call("decoderDen", C), SumOver(g, StabilizerWords(n, C), Pow(F.Id("X"), Call("wt", g)))))));
    }

    private static Formula DecoderNumFormula()
    {
        Formula n = F.Id("n"), C = F.Id("C"), g = F.Id("g");
        return Disp(All("n", Nats(), All("C", Call("CSSCode", n),
            Eq(Call("decoderNum", C), SumOver(g, StabilizerWords(n, C),
                Pow(F.Id("X"), Call("wt", Add(g, Named("one")))))))));
    }

    private static Formula SuppressionOrderFormula()
    {
        Formula n = F.Id("n"), C = F.Id("C"), a = F.Id("a");
        Formula p = Sub(Call("decoderNum", C), Mul(Call("Polynomial.C", a), Call("decoderDen", C)));
        return Disp(All("n", Nats(), All("C", Call("CSSCode", n), All("a", Complexes(),
            Eq(Call("suppressionOrder", C, a), RootMultiplicity(p, a))))));
    }

    private static Formula SuppressionOrderInfFormula()
    {
        Formula n = F.Id("n"), C = F.Id("C"), g = F.Id("g");
        Formula reversed = SumOver(g, StabilizerWords(n, C), Pow(F.Id("X"), Sub(n, Call("wt", g))));
        return Disp(All("n", Nats(), All("C", Call("CSSCode", n),
            Eq(Call("suppressionOrderInf", C), RootMultiplicity(reversed, D(0))))));
    }

    private static Formula FixesWithFormula()
    {
        Formula n = F.Id("n"), C = F.Id("C"), a = F.Id("a");
        Formula body = And(Ne(Call("Polynomial.eval", a, Call("decoderDen", C)), D(0)),
            Eq(Call("Polynomial.eval", a, Call("decoderNum", C)),
                Mul(a, Call("Polynomial.eval", a, Call("decoderDen", C)))));
        return Disp(All("n", Nats(), All("C", Call("CSSCode", n), All("a", Complexes(),
            Eq(Call("FixesWith", C, a), body)))));
    }

    private static Formula FixesWithInfFormula()
    {
        Formula n = F.Id("n"), C = F.Id("C"), g = F.Id("g");
        Formula reversed = SumOver(g, StabilizerWords(n, C), Pow(F.Id("X"),
            Sub(n, Call("wt", Add(g, Named("one"))))));
        return Disp(All("n", Nats(), All("C", Call("CSSCode", n),
            Eq(Call("FixesWithInf", C), Ne(Call("Polynomial.eval", D(0), reversed), D(0))))));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), d = F.Id("d"), C = F.Id("C"), a = F.Id("a");
        Formula points = Mem(a, SetList(D(0), D(1), Seq(Minus, D(1))));
        Formula finite = All("a", Complexes(), Imp(points,
            And(Call("FixesWith", C, a), Le(d, Call("suppressionOrder", C, a)))));
        Formula conclusion = And(finite, And(Call("FixesWithInf", C),
            Le(d, Call("suppressionOrderInf", C))));
        return Disp(All("n", Nats(), All("d", Nats(), All("C", Call("CSSCode", n),
            Imp(Call("HasDistance", C, d), conclusion)))));
    }

    private static Formula At(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);
}
