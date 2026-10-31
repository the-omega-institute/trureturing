using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Experiment;

internal sealed class KBonacciPrefixCompletionDocument : IScribeDocumentDefinition
{
    private const string Root = "D5/S3/ConceptDynamics/Experiment/KBonacciPrefixCompletion.";
    private static Formula Call(string name, params Formula[] args)
    {
        var xs = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (int n = 0; n < args.Length; n++)
        {
            if (n > 0) xs.AddRange([Comma, Sp]);
            xs.Add(args[n]);
        }
        xs.Add(Close);
        return Seq([.. xs]);
    }
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Underscore, Grp(b));
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula K => F.Id("k");
    private static Formula Fin => Call("Fin", K);
    private static Formula Vec => new Formula.TypeArrow(Fin, R);
    private static Formula World => Call("World", K);
    private static Formula Pair => Seq(Fin, Sp, Times, Sp, Fin);
    private static Formula Sets => Call("Finset", Pair);
    private static Formula T(Formula w, Formula i, Formula t) => Call("target", w, i, t);
    private static Formula P(Formula w, Formula r) => Call("cumulative", Call("c", w), Seq(r, Plus, D(1)));
    private static Formula E(Formula w, Formula t) => Sub(Call("ell", w), t);
    private static Formula Data(Formula s, Formula w, Formula v) => Call("SameData", s, w, v);
    private static DocumentBlock.Describe Def(string name, Formula statement, string text) =>
        Describe.Lean(DescribeId.Create("kbonacci-prefix-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Root + name), H(name),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    public DocumentDefinition Create()
    {
        Formula s = F.Id("S"), w = F.Id("w"), v = F.Id("v");
        Formula i = F.Id("i"), t = F.Id("t"), r = F.Id("r"), c = F.Id("c"), j = F.Id("j");
        Formula initial = Call("initial", w);
        Formula off = Call("offDiagonal", K);
        Formula card = Call("card", s);
        Formula budget = Seq(K, Open, K, Minus, D(1), Close);
        Formula product = Seq(P(w,r), E(w,t));
        Formula productsEqual = Seq(product, Sp, Eq, Sp, P(v,r), E(v,t));
        Formula pair = Seq(Open, r, Comma, t, Close);
        Formula selected = Seq(pair, Sp, InMacro, Sp, s);
        Formula equalTarget = All("i", Fin, All("t", Fin, Eqn(T(w,i,t),T(v,i,t))));
        Formula same = Seq(Eqn(initial,Call("initial",v)), Sp, Land, Sp,
            All("r", Fin, All("t", Fin, Seq(selected, Sp, Implies, Sp, productsEqual))));
        Formula worldLaw = Seq(
            OpenBrace, Open, c, Comma, F.Id("l"), Close, Colon, Sp,
            Vec, Sp, Times, Sp, Vec, Sp, Vert, Sp, Open, All("i", Fin, Seq(D(0), Sp, Lt, Sp, Sub(c,i))), Close, Sp, Land, Sp,
            Open, All("i", Fin, Seq(D(0), Sp, Leq, Sp, Sub(F.Id("l"),i))), Close,
            Sp, Land, Sp, F.Id("l"), Sp, Neq, Sp, D(0), CloseBrace);
        return DocumentDefinition.Create(ScribeNode.Create(
            "Exact recovery and classification of cumulative products with an unknown nonnegative reader.",
            H("KBonacci Prefix Completion"), Blocks(
            Def("World", All("k",N,Eqn(World,worldLaw)),
                "The two factors are real vectors indexed by Fin k. Every object coordinate is strictly positive; the fixed reader is nonnegative and nonzero. Its support is unknown. No normalization or symmetry is imposed."),
            Def("target", All("k",N,All("w",World,All("i",Fin,All("t",Fin,
                Eqn(T(w,i,t),Seq(Sub(Call("c",w),i),E(w,t))))))),
                "The target is the initial outer product. Opposite rescaling of its two factors does not change this target."),
            Def("cumulative", All("k",N,All("c",Vec,All("j",N,
                Eqn(Call("cumulative",c,j),Seq(Sum,Underscore,Grp(Seq(i,Colon,Sp,Fin,Comma,Sp,i,Sp,Lt,Sp,j)),Sub(c,i)))))),
                "The cumulative value is the sum over coordinates smaller than the natural prefix length j. It is zero at j = 0 and strictly positive for each nonempty prefix of a positive object."),
            Def("initial", All("k",N,All("w",World,Eqn(initial,
                Seq(Sum,Underscore,Grp(Seq(i,Colon,Sp,Fin)),Sub(Call("c",w),i),E(w,i))))),
                "This is the mandatory preparation reading. Every preparation of the same object with the same reader has this value."),
            Def("offDiagonal", All("k",N,Eqn(off,Seq(OpenBrace,pair,Colon,Sp,Pair,
                Sp,Vert,Sp,r,Sp,Neq,Sp,t,CloseBrace))),
                "Row r denotes source prefix length j = r + 1. The off-diagonal set therefore omits precisely the source positions j = t + 1."),
            Def("SameData", All("k",N,All("S",Sets,All("w",World,All("v",World,
                Seq(Data(s,w,v),Sp,Iff,Sp,Open,same,Close))))),
                "Two worlds have the same selected data when their paid initial readings agree and every selected prefix product agrees. Repetitions add no distinct coordinate to this finite set."),
            Def("Identifies", All("k",N,All("S",Sets,Seq(Call("Identifies",s),Sp,Iff,Sp,
                All("w",World,All("v",World,Seq(Data(s,w,v),Sp,Implies,Sp,equalTarget)))))),
                "Identifiability means constancy of the initial relation on each selected-data fiber over the whole world domain."),
            Def("column", All("k",N,All("S",Sets,All("t",Fin,
                Eqn(Call("column",s,t),Seq(OpenBrace,r,Colon,Sp,Fin,Sp,Vert,Sp,selected,CloseBrace))))),
                "A column contains the distinct selected prefix rows for one reader coordinate."),
            Describe.Lean(DescribeId.Create("kbonacci-off-diagonal-identifies"),
                DeclarationHandle.Create(Root + "off_diagonal_identifies"),
                H("Recovery on every nonempty reader support"),
                StatementSource.FromAuthor(Disp(All("k",N,Seq(D(3),Sp,Leq,Sp,K,Sp,Implies,Sp,Call("Identifies",off))))),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Observed positive-prefix products determine exactly which reader coordinates vanish. With a single active coordinate t, the paid initial reading supplies its missing adjacent prefix increment, including the first and last coordinate boundaries.")),
                    Paragraph(Text("With two active columns a and b, a third row is available because k is at least three. Products on that common row determine the relative reader scale. The other active column fills the missing row of column a, and every remaining column is then determined, including zero columns. Differences of adjacent cumulative products yield every initial relation entry."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("kbonacci-endpoint-pattern-classification"),
                DeclarationHandle.Create(Root + "endpoint_pattern_classification"),
                H("Classification at the distinct-product budget"),
                StatementSource.FromAuthor(Disp(All("k",N,Seq(D(3),Sp,Leq,Sp,K,Sp,Implies,Sp,
                    All("S",Sets,Seq(card,Sp,Leq,Sp,budget,Sp,Implies,Sp,
                        Open,Call("Identifies",s),Sp,Iff,Sp,Eqn(s,off),Close)))))),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("A singleton-support reader forces at least k - 1 distinct prefixes in each column: otherwise the coordinate reading and those prefix sums have a nonzero common kernel direction. The positive objects with coordinates abs(h) + 1 and abs(h) + 1 + h realize a collision in the full world domain.")),
                    Paragraph(Text("The budget forces exactly one omitted prefix in each column. A perturbation supported on adjacent object coordinates shows that this omission must lie next to the column index. Starting at the first column, a reader supported on two neighboring columns excludes the remaining incorrect omission. Thus every omitted row equals its column index.")),
                    Paragraph(Text("This theorem concerns selected cumulative scalar products. The connection to literal legal words, sequential irreversible actions and ordered compulsory paid records is established separately by the actual-record theorem. No continuity or computational condition on a final decoder is used."))), DescribeRole.Theorem))));
    }
}
