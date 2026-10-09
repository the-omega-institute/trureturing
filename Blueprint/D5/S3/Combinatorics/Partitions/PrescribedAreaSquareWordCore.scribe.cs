using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class PrescribedAreaSquareWordCoreDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/PrescribedAreaSquareWordCore.";
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula I(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(I(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, I(name), Sp, InMacro, Sp, type, Comma, Sp, body);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Lt(Formula a, Formula b) => Seq(a, Sp, F.Lt, Sp, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Sp, Minus, Sp, b);
    private static Formula Mul(Formula a, Formula b) => Seq(a, Sp, Times, Sp, b);
    private static Formula Paren(Formula a) => Seq(Open, a, Close);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Paren(a), b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula And(params Formula[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.AddRange([Sp, Land, Sp]);
            items.Add(Paren(part));
        }
        return Seq([.. items]);
    }
    private static Formula Fun(Formula body) =>
        Call("fun", Seq(I("x"), Colon, CoreIndex), body);
    private static Formula Card(Formula body) => Call("ncard", Call("range", Fun(body)));
    private static Formula Inj(Formula body) => Call("Injective", Fun(body));
    private static Formula A => Call("coreSide", I("J"));
    private static Formula Q => Call("q", I("J"));
    private static Formula K => Call("suffixArea", I("J"), I("h"), I("t"));
    private static Formula Z => Call("fixedZ", Sub(I("h"), A), K);
    private static Formula Vx => Call("V", I("J"), I("x"));
    private static Formula Wx => Call("W", I("J"), I("h"), I("t"), I("x"));
    private static Formula Rows(Formula w) => Call("rows", w);
    private static Formula G(Formula w) => Call("G", w);
    private static Formula Field(string name, Formula w) => Call(name, G(w));
    private static Formula Count(Formula w, string c) => Call("count", w, I(c));
    private static Formula Area(Formula w) => Call("scatteredTrueFalseCount", w);
    private static Formula X => Call("val", Call("fst", I("x")));
    private static Formula Y => Call("val", Call("snd", I("x")));
    private static Formula CoreE => Sub(Sub(Mul(Seq(Minus, D(9, 2)),
        Paren(Sub(Pow(Q, D(3)), D(1)))), Mul(D(2, 4), X)), Mul(D(1, 2), Y));
    private static Formula CoreF => Sub(Sub(Mul(Seq(Minus, D(1, 3, 6)),
        Paren(Sub(Pow(Q, D(3)), D(1)))), Mul(D(1, 2), X)), Mul(D(2, 4), Y));
    private static Formula Joint => Call("Pair", Field("e", Wx), Field("f", Wx));
    private static Formula RowJoint => Call("Pair", Call("squareRows", Rows(Wx)),
        Call("oddRows", Rows(Wx)));
    private static Formula CoreIndex => Call("CoreIndex", I("J"));

    private static Formula SquareFormula()
    {
        var core = All("x", CoreIndex, And(
            Eqn(G(Vx), Call("Five", A, A, D(0), CoreE, CoreF)),
            Eqn(Count(Vx, "true"), A), Eqn(Count(Vx, "false"), A),
            Eqn(Area(Vx), Div(Pow(A, D(2)), D(2)))));
        var guards = And(Lt(D(0), Sub(I("h"), A)), Call("Even", A),
            Le(Mul(A, I("h")), Add(I("t"), Div(Pow(A, D(2)), D(2)))),
            Eqn(Add(K, Mul(A, I("h"))), Add(I("t"), Div(Pow(A, D(2)), D(2)))),
            Le(K, Pow(Sub(I("h"), A), D(2))));
        var perWord = All("x", CoreIndex, And(
            Seq(Wx, Sp, InMacro, Sp, Call("wordFiber", I("h"), I("h"), I("t"))),
            Eqn(Count(Wx, "true"), I("h")), Eqn(Count(Wx, "false"), I("h")),
            Eqn(Area(Wx), I("t")), Eqn(Call("length", Rows(Wx)), I("h")),
            Call("SortedGE", Rows(Wx)), All("r", Rows(Wx), Le(I("r"), I("h"))),
            Eqn(Call("sum", Rows(Wx)), I("t")),
            Eqn(Rows(Wx), Call("append", Call("map", Rows(Z),
                Call("fun", I("r"), Add(I("r"), A))), Rows(Vx))),
            Eqn(G(Wx), Call("Five", I("h"), I("h"),
                Sub(Mul(D(2), I("t")), Pow(I("h"), D(2))),
                Add(Add(CoreE, Field("e", Z)), Mul(Mul(D(3), A), Field("d", Z))),
                Add(Add(CoreF, Field("f", Z)), Mul(Mul(D(3), A), Field("d", Z)))))));
        var hypotheses = And(Lt(D(0), I("h")), Le(Mul(D(8), A), I("h")),
            Le(Pow(I("h"), D(2)), Mul(D(8), I("t"))),
            Le(Mul(D(8), I("t")), Mul(D(7), Pow(I("h"), D(2)))));
        return All("J", N, All("h", N, All("t", N, Seq(hypotheses, Sp, Implies, Sp,
            And(core, guards, perWord, Inj(Wx), Inj(Joint), Inj(RowJoint),
                Eqn(Card(Wx), Pow(Q, D(6))), Eqn(Card(Joint), Pow(Q, D(6))),
                Eqn(Card(RowJoint), Pow(Q, D(6))),
                Le(Pow(Q, D(6)), Call("capacity", I("h"), I("h"), I("t"))))))));
    }

    private static DocumentBlock Def(string id, string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal expansion, ordered base-eight source blocks and exact-area square words with a common joint moment image.",
        H("Prescribed-area square word core"), Blocks(
            Def("level-three-index", "level3Index", "Level-three Boolean indices",
                "The index is the function with values x,y,z on Fin 3. True denotes a and false denotes b."),
            Def("source-p-zero", "P0", "The first P source", "P0 is the positivePairWords second component at index (true,false,true), the literal baaab."),
            Def("source-p-one", "P1", "The second P source", "P1 is the first component at that same index, the literal ababa."),
            Def("source-q-zero", "Q0", "The first Q source", "Q0 is the second component at index (true,false,false), the literal babab."),
            Def("source-q-one", "Q1", "The second Q source", "Q1 is the first component at that same index, the literal abbba."),
            Def("source-block", "H", "The four selected blocks",
                "H(e,f) is P_e followed by Q_f,Q0,P0. Its counts are (10,10), its scattered ab area is 50, and its G coordinates are (10,10,0,−92−24e−12f,−136−12e−24f), with Boolean values represented by zero or one."),
            Describe.Lean(DescribeId.Create("literal-power-rows"), DeclarationHandle.Create(Prefix + "rows_literalPowerWord"),
                H("Rows of the actual repeated word"), StatementSource.FromAuthor(Disp(
                    All("n", N, All("w", Call("List", I("Bool")), Eqn(
                        Rows(Call("literalPowerWord", I("n"), I("w"))),
                        Call("flatMap", Rows(I("w")), Call("fun", I("r"),
                            Call("replicate", I("n"), Mul(I("n"), I("r")))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Each actual row is repeated n times and multiplied by n. The identity includes n=0 and the empty word."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("literal-power-geometry"), DeclarationHandle.Create(Prefix + "G_literalPowerWord"),
                H("Homogeneity of the actual fan"), StatementSource.FromAuthor(Disp(
                    All("n", N, All("w", Call("List", I("Bool")), Eqn(
                        G(Call("literalPowerWord", I("n"), I("w"))), Call("Five",
                            Mul(I("n"), Field("u", I("w"))), Mul(I("n"), Field("v", I("w"))),
                            Mul(Pow(I("n"), D(2)), Field("d", I("w"))),
                            Mul(Pow(I("n"), D(3)), Field("e", I("w"))),
                            Mul(Pow(I("n"), D(3)), Field("f", I("w"))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The row identity scales area quadratically and both the square-row and odd-row sums cubically. The existing actual fan formulas then give all five homogeneous coordinates."))), DescribeRole.Theorem),
            Def("dyadic-radix", "q", "Dyadic radix", "q(J)=2^J."),
            Def("core-side", "coreSide", "Core side", "coreSide(J)=70(q(J)−1), an even natural number."),
            Def("core-index", "CoreIndex", "The full core index domain", "CoreIndex(J)=Fin(q(J)^3) × Fin(q(J)^3)."),
            Def("ordered-core", "V", "The actual ordered core",
                "Use Nat.digitsAppend 8 J for both coordinates. In increasing scale i, concatenate the seven thresholds ℓ=1,…,7 of H(ℓ≤d_i,ℓ≤e_i), with each letter repeated 2^i times. For J=0 this is an auxiliary empty word contribution; it is not a native empty tree."),
            Def("exact-suffix", "fixedZ", "The exact quotient/remainder suffix",
                "For b>0 and 0≤κ≤b², let j=κ/b and z=κ mod b. At z=0 use b^(b−j)a^b b^j; otherwise use b^(b−j−1)a^z b a^(b−z)b^j. Its direct rows are j copies of b, followed when z>0 by z, followed by the required zero padding. The exponent guards include κ=0 and κ=b²."),
            Def("suffix-area", "suffixArea", "Suffix area",
                "suffixArea(J,h,t)=t+coreSide(J)²/2−coreSide(J)h in natural arithmetic. The square hypotheses prove nontruncation and the upper bound (h−coreSide(J))² before this subtraction is used."),
            Def("completed-word", "W", "The completed square word",
                "W(J,h,t,x)=V(J,x) followed by fixedZ(h−coreSide(J),suffixArea(J,h,t)). The suffix is fixed across the full core index domain."),
            Describe.Lean(DescribeId.Create("exact-square-family"), DeclarationHandle.Create(Prefix + "square_family"),
                H("Exact area and simultaneous joint injection"), StatementSource.FromAuthor(Disp(SquareFormula())),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For every natural J,h,t with h>0, 8a≤h and h²≤8t≤7h², the actual words have counts (h,h), area exactly t and h sorted direct rows bounded by h. Membership in wordFiber includes nonemptiness. The core has zero D, while the completed square has D=2t−h². Concatenation translates the suffix rows by a and adds the fixed moment vector (E_Z+3aD_Z,F_Z+3aD_Z). For μ=rows(W), the direct fan formulas give E=h³−6ht+6 squareRows(μ) and F=−h³+6ht−6 oddRows(μ); the latter statistic is the square-column sum of the same Ferrers diagram. The independent core directions (−24,−12) and (−12,−24) have determinant 432. Consequently the same actual word supplies both moments, and its squareRows and oddRows pair is also injective. Each of the word, joint fan and joint row-statistic images has exactly q^6 elements, giving that lower bound in the existing whole word-fiber capacity. J=0 is included. The direct area t is preserved even above h²/2, without reversing the core."))),
                DescribeRole.Theorem))));
}
