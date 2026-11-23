using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class FourVertexPortPulsesDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Observer/Linear/FourVertexPortPulses.";

    private static readonly Formula
        M = F.Id("M"), Q = F.Id("q"), G = GammaLower, R = MathbbR(),
        L = F.Id("L"), X = F.Id("x"), B = F.Id("b"), U = F.Id("U"),
        Rho = F.Id("r"), S = F.Id("S"), W = F.Id("w"), T = F.Id("T"),
        Age = F.Id("t"), I = F.Id("i"), J = F.Id("j"),
        Bool = F.Id("Bool"), Matrix = Seq(R, Caret, Grp(D(4), Times, D(4))), FinsetR = Call(F.Id("Finset"), R),
        Weights = new Formula.TypeArrow(R, R);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact four-age preparation", H("Exact four-age preparation at a reflected graph port"), Blocks(
            Node("port", "Raw port", Disp(Seq(B, Eq, Tuple(D(1), D(0), D(0), D(0)), Caret, Grp(F.Id("T")))),
                "The actuator injects at vertex zero of the labelled graph.", DescribeRole.Definition),
            Node("target", "Centered target", Disp(Seq(X, Eq, Frac, Grp(D(1)), Grp(Sqrt, Grp(D(1, 4))),
                Tuple(Seq(Minus, D(3)), D(0), D(1), D(2)), Caret, Grp(F.Id("T")))),
                "The target has unit Euclidean norm and zero total mass.", DescribeRole.Definition),
            Node("reflection", "Reflection", Disp(Seq(U, Eq, F.Id("I"), Minus, Frac, Grp(D(1)), Grp(D(3)),
                F.Id("v"), F.Id("v"), Caret, Grp(F.Id("T")))),
                "The hidden direction is v=(0,1,−2,1) in vertex order. The reflection fixes the port and the target.",
                DescribeRole.Definition),
            Node("laplacian", "Labelled graph pair", GraphFormula(),
                "Let P project off the constant vector. The vector h is (0,−1,0,1) in vertex order. The signed star E adds the rank-one edge Laplacian for edge (0,i) with coefficient gamma times v_i divided by two. The false label gives the uniform generator (M/8)P plus E and the hidden coupling. The true label gives its conjugate by the reflection.",
                DescribeRole.Definition),
            Node("endpoint", "Raw signed endpoint", Disp(Seq(Forall, Sp, L, Colon, Matrix, Comma, Sp, S, Colon, FinsetR,
                Comma, Sp, W, Colon, Weights, Comma, Sp,
                Call(F.Id("endpoint"), L, S, W), Eq, Sum, Underscore, Grp(Age, InMacro, Sp, S),
                Call(W, Age), Sp, Exp, Open, Minus, Age, L, Close, Sp, B)),
                "Here L is a four by four real matrix and S is a finite set of real ages.",
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("exact-four-ages"), DeclarationHandle.Create(Gid + "exact_four_ages"),
                H("Four distinct raw ages are necessary and sufficient"), StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The two matrices are positive semidefinite, have zero row sums, and give strictly positive conductances at every pair of distinct vertices. The same signed recipe works on the two labelled graphs because the reflection fixes both the input port and the target.")),
                    Paragraph(Text("The determinant equation for the centered Jacobi block gives one root in each of the intervals (−2 gamma,−gamma), (0,gamma/2) and (gamma,2 gamma). After shifting by M/8 the three roots give positive rates with nonzero port coordinates. Dividing the corresponding target coordinates by the port coordinates gives signs negative, positive, negative in increasing order of rate.")),
                    Paragraph(Text("The scalar pulse response vanishes at rate zero by mass conservation. The three centered values give two further distinct zeros by continuity. The exponential zero bound prohibits this response with fewer than four distinct ages, including when age zero or arbitrary real pulse weights are allowed.")),
                    Paragraph(Text("At any four distinct ages the exponential interpolation system is invertible by the same zero bound. Prescribing the zero mass mode and the three centered ratios gives the exact endpoint. Ages T/4, T/2, 3T/4 and T provide one choice in every positive horizon.")),
                    Paragraph(Ref("D5/S3/Analytic/ExponentialSum/DescartesRule.zero_bound"))),
                DescribeRole.Theorem))));

    private static Formula MathbbR() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Tuple(params Formula[] items) => Call(Grp(), items);

    private static Formula Call(Formula name, params Formula[] items)
    {
        var parts = new List<Formula> { name, Open };
        foreach (var item in items)
        {
            if (parts.Count > 2) parts.AddRange([Comma, Sp]);
            parts.Add(item);
        }
        parts.Add(Close);
        return Seq([.. parts]);
    }

    private static Formula Lap(Formula r) => Call(L, M, G, Q, r);

    private static Formula GraphFormula()
    {
        Formula f = F.Id("false"), t = F.Id("true"), p = F.Id("P"), e = F.Id("E");
        Formula v = F.Id("v"), h = F.Id("h"), transpose = Caret;
        return Disp(Seq(Forall, Sp, M, Comma, G, Comma, Q, Colon, Sp, R, Comma, Sp,
            Lap(f), Eq, Frac, Grp(M), Grp(D(8)), p, Plus, Call(e, G), Plus,
            Frac, Grp(Q), Grp(D(2), Sqrt, Grp(D(3))),
            Open, v, h, transpose, Grp(F.Id("T")), Plus, h, v, transpose, Grp(F.Id("T")), Close,
            Sp, Land, Sp, Lap(t), Eq, U, Lap(f), U, transpose, Grp(F.Id("T"))));
    }

    private static Formula TheoremFormula()
    {
        Formula bindAges = Seq(S, Colon, FinsetR);
        Formula bindWeights = Seq(W, Colon, Weights);
        Formula card = Seq(Lvert, Sp, S, Rvert);
        Formula net = Seq(Sum, Underscore, Grp(Age, InMacro, Sp, S), Call(W, Age), Eq, D(0));
        Formula eq = Seq(Call(F.Id("endpoint"), Lap(Rho), S, W), Eq, X);
        Formula both = Seq(Forall, Sp, Rho, Colon, Bool, Comma, eq);
        return Disp(Seq(Begin, Grp(F.Id("gathered")),
            Forall, Sp, M, Comma, G, Comma, Q, Colon, Sp, R, Comma, Sp,
            D(0), Lt, M, Land, Sp, D(0), Lt, G, Le, Frac, Grp(M), Grp(D(2, 5, 6)),
            Land, Sp, D(0), Lt, Q, Le, Frac, Grp(G, Caret, Grp(D(2))), Grp(M), Sp,
            Longrightarrow, Sp, RowBreak, Grp(),
            Open, Forall, Sp, Rho, Colon, Bool, Comma,
            Call(F.Id("PosSemidef"), Lap(Rho)), Land, Sp,
            Open, Forall, Sp, I, Comma, Sum, Underscore, Grp(J),
            Call(Lap(Rho), I, J), Eq, D(0), Close, Land, Sp,
            Open, Forall, Sp, I, Comma, J, Comma, I, Neq, Sp, J, Rightarrow, Sp,
            D(0), Lt, Minus, Call(Lap(Rho), I, J), Close, Close, Land, Sp, RowBreak, Grp(),
            Open, Forall, Sp, Rho, Colon, Bool, Comma, bindAges, Comma, bindWeights, Comma,
            eq, Rightarrow, Sp, D(4), Le, card, Land, Sp, net, Close, Land, Sp, RowBreak, Grp(),
            Open, Forall, Sp, bindAges, Comma, card, Eq, D(4), Rightarrow, Sp,
            Exists, Sp, bindWeights, Comma, net, Land, Sp, Open, both, Close, Close,
            Land, Sp, RowBreak, Grp(),
            Open, Forall, Sp, T, Colon, R, Comma, D(0), Lt, T, Rightarrow, Sp,
            Exists, Sp, bindAges, Comma, bindWeights, Comma, card, Eq, D(4), Land, Sp,
            Open, Forall, Sp, Age, InMacro, Sp, S, Comma, D(0), Lt, Age, Land, Sp, Age, Le, Sp, T,
            Close, Land, Sp, net, Land, Sp, Open, both, Close, Close,
            End, Grp(F.Id("gathered"))));
    }

    private static DocumentBlock Node(string name, string title, Formula statement, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("four-vertex-" + name), DeclarationHandle.Create(Gid + name),
            H(title), StatementSource.FromAuthor(statement), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
