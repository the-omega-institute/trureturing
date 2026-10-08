using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition;

internal sealed class CoprimeSingletonCostDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var Y = F.Id("Y"); var k = F.Id("k"); var m = F.Id("m"); var j = F.Id("j");
        var A = F.Id("A"); var B = F.Id("B"); var bottom = F.Id("bottom");
        var v = F.Id("v"); var a = F.Id("a"); var d = F.Id("D"); var labels = F.Id("labels");
        var pi = F.Id("pi"); var trees = F.Id("trees"); var i = F.Id("i"); var s = F.Id("s");
        var initial = F.Id("initial"); var archive = F.Id("archive"); var word = F.Id("word");
        var entry = F.Id("entry"); var t = F.Id("t"); var w = F.Id("w"); var c = F.Id("c");
        var n = F.Id("n"); var nat = Seq(Mathbb, Grp(F.Id("N"))); var boolType = F.Id("Bool");
        var observation = Call("Option", Call("ZMod", D(2)));
        var period = Add(k, D(1)); var gcd = Call("gcd", m, period);
        var index = Call("Fin", Call("div", period, gcd));
        var nil = Seq(OpenBracket, CloseBracket); var none = F.Id("none");
        var somev = Call("some", v);
        var entryType = Call("Prod", Call("AllowedBlock", k, m, a), observation);
        var projection = Seq(Open, LambdaLower, Sp, Open, entry, Colon, entryType, Close,
            Comma, Sp, Open, Call("val", Call("fst", entry)), Comma, Call("snd", entry), Close, Close);
        var tree = new Formula.Apply(trees, [somev]);
        var record = Call("some", Seq(Open, v, Comma,
            new Formula.Negate(Call("cast", Call("val", i), Call("ZMod", period))), Comma, s, Close));
        var actualArchive = Call("archive", tree, record);
        var length = Call("length", actualArchive);
        var label = new Formula.Apply(labels, [i]);
        var noNone = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("entry"),
            entryType, new Formula.Logic(
                new Formula.Relation(entry, FormulaRelationOperator.MemberOf, actualArchive),
                FormulaLogicOperator.Implies, NotEqual(Call("snd", entry), none)));
        var prefix = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("t"), nat,
            new Formula.Logic(new Formula.Relation(t, FormulaRelationOperator.LessThan, length),
                FormulaLogicOperator.Implies, Equal(
                    new Formula.Apply(pi, [somev, Call("map", Call("take", t, actualArchive), projection)]),
                    Call("inr", Call("val", Call("fst", Call("get", actualArchive, t)))))));
        var nativeClauses = new List<Formula>
        {
            Equal(Call("result", tree, record), label),
            new Formula.Relation(length, FormulaRelationOperator.LessThanOrEqual, d),
            noNone, prefix,
            Equal(new Formula.Apply(pi, [somev, Call("map", actualArchive, projection)]), Call("inl", label))
        };
        Formula nativeBody = nativeClauses[^1];
        for (var x = nativeClauses.Count - 2; x >= 0; x--)
            nativeBody = new Formula.Logic(nativeClauses[x], FormulaLogicOperator.And, nativeBody);
        var native = new Formula.BindMany(FormulaQuantifier.ForAll,
            [new(FormulaIdentifier.Create("i"), index), new(FormulaIdentifier.Create("s"), nat)],
            new Formula.Logic(new Formula.Relation(s, FormulaRelationOperator.LessThan, k),
                FormulaLogicOperator.Implies, nativeBody));
        var original = Call("OriginalRecord", k, w);
        var rawResult = new Formula.Logic(
            new Formula.Relation(c, FormulaRelationOperator.LessThanOrEqual, d),
            FormulaLogicOperator.And, new Formula.Logic(
                Equal(Call("execute", k, pi, d, w, somev, nil),
                    Call("some", Seq(Open, label, Comma, c, Close))),
                FormulaLogicOperator.And, new Formula.Logic(
                    Equal(Call("result", tree, original), label), FormulaLogicOperator.And,
                    Equal(Call("length", Call("archive", tree, original)), c))));
        var raw = new Formula.BindMany(FormulaQuantifier.ForAll,
            [new(FormulaIdentifier.Create("w"), Call("List", boolType)),
             new(FormulaIdentifier.Create("i"), index)],
            new Formula.Logic(new Formula.Relation(m, FormulaRelationOperator.Divides, Call("length", w)),
                FormulaLogicOperator.Implies, new Formula.Logic(Equal(Call("output", k, w), somev),
                    FormulaLogicOperator.Implies, new Formula.Logic(
                        new Formula.Relation(period, FormulaRelationOperator.Divides,
                            Add(Call("length", w), Multiply(Call("val", i), gcd))),
                        FormulaLogicOperator.Implies,
                        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("c"), nat, rawResult)))));
        var legal = new Formula.BindMany(FormulaQuantifier.ForAll,
            [new(FormulaIdentifier.Create("initial"), observation),
             new(FormulaIdentifier.Create("archive"), Call("Archive", m)),
             new(FormulaIdentifier.Create("word"), new Formula.TypeArrow(Call("Fin", m), boolType))],
            new Formula.Logic(Equal(new Formula.Apply(pi, [initial, archive]), Call("inr", word)),
                FormulaLogicOperator.Implies, new Formula.Logic(Equal(a, F.Id("true")),
                    FormulaLogicOperator.Implies, Call("DBonacciAdmissible", k, m, word))));
        var rejectedTree = new Formula.Apply(trees, [none]);
        var witnessClauses = new List<Formula>
        {
            legal, Equal(new Formula.Apply(pi, [none, nil]), Call("inl", bottom)),
            Equal(Call("result", rejectedTree, none), bottom),
            Equal(Call("archive", rejectedTree, none), nil), native, raw
        };
        Formula witnessBody = witnessClauses[^1];
        for (var x = witnessClauses.Count - 2; x >= 0; x--)
            witnessBody = new Formula.Logic(witnessClauses[x], FormulaLogicOperator.And, witnessBody);
        var witness = new Formula.BindMany(FormulaQuantifier.Exists,
            [new(FormulaIdentifier.Create("pi"), Call("Selector", m, Y)),
             new(FormulaIdentifier.Create("trees"), new Formula.TypeArrow(observation,
                 Call("AcquisitionTree", k, m, a, Y, d)))], witnessBody);
        var budgets = Seq(OpenBrace, n, Colon, nat, Sp, Bar, Sp,
            Call("Feasible", k, m, a, labels, bottom, v, n), CloseBrace);
        var conclusion = new Formula.Logic(Call("IsLeast", budgets, d), FormulaLogicOperator.And, witness);
        var labelFunction = Seq(Open, LambdaLower, Sp, Open, i, Colon, index, Close, Comma, Sp,
            Call("ite", Equal(Call("val", i), j), B, A), Close);
        var localConclusion = Seq(Operatorname, Grp(F.Id("let")), Sp, d, Eq,
            Call("max", D(2), Call("ceilDiv", j, m)), Sp, Operatorname, Grp(F.Id("in")), Sp,
            Open, Operatorname, Grp(F.Id("let")), Sp, labels, Eq, labelFunction, Sp,
            Operatorname, Grp(F.Id("in")), Sp, Open, conclusion, Close, Close);
        var hypotheses = new List<Formula>
        {
            new Formula.Relation(D(2), FormulaRelationOperator.LessThanOrEqual, k),
            new Formula.Relation(D(2), FormulaRelationOperator.LessThanOrEqual, m),
            new Formula.Relation(m, FormulaRelationOperator.LessThan, k), Call("Coprime", m, period),
            new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, j),
            new Formula.Relation(j, FormulaRelationOperator.LessThanOrEqual, k), NotEqual(A, B)
        };
        Formula assumptions = hypotheses[^1];
        for (var x = hypotheses.Count - 2; x >= 0; x--)
            assumptions = new Formula.Logic(hypotheses[x], FormulaLogicOperator.And, assumptions);
        var statement = new Formula.BindMany(FormulaQuantifier.ForAll,
            [new(FormulaIdentifier.Create("Y"), F.Id("Type")),
             new(FormulaIdentifier.Create("k"), nat), new(FormulaIdentifier.Create("m"), nat),
             new(FormulaIdentifier.Create("j"), nat), new(FormulaIdentifier.Create("A"), Y),
             new(FormulaIdentifier.Create("B"), Y), new(FormulaIdentifier.Create("bottom"), Y),
             new(FormulaIdentifier.Create("v"), Call("ZMod", D(2))),
             new(FormulaIdentifier.Create("a"), boolType)],
            new Formula.Logic(assumptions, FormulaLogicOperator.Implies, localConclusion));
        return DocumentDefinition.Create(ScribeNode.Create(
        "Coprime nonzero initial phase singletons have exact safe complete-block cost.",
        H("Exact acquisition cost of a coprime phase singleton"),
        Blocks(Describe.Lean(
            DescribeId.Create("coprime-nonzero-singleton-cost"),
            DeclarationHandle.Create(
                "D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/"
                + "CoprimeSingletonCost.coprime_nonzero_singleton_cost"),
            H("The least budget is the maximum of two and the paid arrival time"),
            StatementSource.FromAuthor(Disp(statement)),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Feasible, Selector, Archive, output and execute denote the original "
                    + "NarrowWindowCost objects. OriginalRecord is the original scanner record. "
                    + "Proof arguments are suppressed. The bounded get operation uses its displayed "
                    + "strict index bound, and the archive map projects each AllowedBlock to its word.")),
                Paragraph(Text(
                    "For every k>=2, 2<=m<k, gcd(m,k+1)=1 and 1<=j<=k, the INITIAL "
                    + "phase index j receives label B and every other index receives label A. "
                    + "The label type, distinct A and B, initial-bottom label and free value v "
                    + "are arbitrary. For either complete-block alphabet the least raw feasible "
                    + "budget is max(2,ceil(j/m)). The lower bound ranges over all adaptive "
                    + "selectors, including selectors whose actions reject.")),
                Paragraph(Text(
                    "One attaining selector and its endpoint trees witness this same budget. "
                    + "Initial rejection stops freely with the bottom label and an empty archive. "
                    + "Every legal INITIAL tail returns the INITIAL singleton label, and every "
                    + "recorded endpoint is some value. At each strict archive prefix the selector "
                    + "issues its recorded complete word; on the complete archive it stops with "
                    + "that INITIAL label. For every actual initial history the raw execution, "
                    + "tree result and charged archive length agree.")),
                Paragraph(Text(
                    "Literal root and repair words provide the near cases. Remote targets use "
                    + "paid zero blocks, a pulse and a final word; empty waits and zero final "
                    + "padding are included. Actual initial histories are realized in the original "
                    + "scanner, and every raw feasible selector induces an endpoint tree.")),
                Paragraph(Text("The universal endpoint-tree obstruction in "),
                    Ref("D5/S3/ObserverMemory/Algorithms/KBonacciAcquisition/CoprimeSingletonLower"),
                    Text(" combines absorbing rejection, even one-block charge and "
                        + "indistinguishability before paid arrival. The same literal marker "
                        + "equations also govern the attaining root, repair and pulse words."))),
            DescribeRole.Theorem))));
    }
}
