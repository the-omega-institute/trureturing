using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.InverseLimits;

internal sealed class FunctionGraphSpectrumCollisionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal trace and rank spectra do not determine an eight-state functional graph.",
        H("Function-Graph Spectrum Collision"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("same-spectra-but-nonconjugate-functional-graphs"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/InverseLimits/FunctionGraphSpectrumCollision."
                    + "same_trace_rank_spectra_not_function_graph_conjugate"),
                H("The complete spectra agree while the functional graphs do not"),
                StatementSource.FromAuthor(CollisionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Identify 0,a,b,c,d,e,f,g with Fin 8 in that order. The displayed "
                            + "sixteen equations are the complete tables of tauA and tauB. "
                            + "The rank value is the cardinality of the iterated image, and the "
                            + "trace value is the number of fixed points of the iterate.")),
                    Paragraph(Text(
                        "A leaf has no predecessor. The depth-one leaf multiset collects the "
                            + "leaf counts at the non-root children mapped directly to 0. Its "
                            + "values are {3,1,0} and {2,2,0}.")),
                    Paragraph(Text(
                        "A functional-graph isomorphism is expressed without a new classifier: "
                            + "it is a permutation semiconjugating tauA to tauB. Such a map would "
                            + "preserve every fiber cardinality, but tauA has a fiber of size "
                            + "three and tauB has none, so no conjugacy exists.")),
                    Paragraph(Text(
                        "Repository and pinned-Mathlib searches found no equal or stronger "
                            + "statement. Mathlib supplies Semiconj, iterate_add_apply, "
                            + "image_const, and card_congr; GitHub Lean-code search found only "
                            + "those building blocks and mirrors."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula FinEight() => Apply(F.Id("Fin"), D(8));

    private static Formula Multiset(params byte[] entries)
    {
        var items = new List<Formula> { OpenBrace };
        for (var index = 0; index < entries.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(D(entries[index]));
        }
        items.Add(CloseBrace);
        return Seq([.. items]);
    }

    private static Formula TableEntry(Formula function, byte input, byte output) =>
        Seq(Apply(function, D(input)), Sp, Eq, Sp, D(output));

    private static Formula CollisionFormula()
    {
        Formula a = F.Id("tauA");
        Formula b = F.Id("tauB");
        Formula x = F.Id("x");
        Formula k = F.Id("k");
        Formula rankA = Apply(F.Id("rankSpectrumValue"), a, k);
        Formula rankB = Apply(F.Id("rankSpectrumValue"), b, k);
        Formula traceA = Apply(F.Id("traceSpectrumValue"), a, k);
        Formula traceB = Apply(F.Id("traceSpectrumValue"), b, k);
        Formula leavesA = Apply(F.Id("depthOneLeafMultiset"), a);
        Formula leavesB = Apply(F.Id("depthOneLeafMultiset"), b);
        Formula equivPerm = Apply(
            Seq(F.Id("Equiv"), Dot, F.Id("Perm")), FinEight());

        return Disp(Seq(
            TableEntry(a, 0, 0), Sp, Land, Sp,
            TableEntry(a, 1, 0), Sp, Land, Sp,
            TableEntry(a, 2, 0), Sp, Land, Sp,
            TableEntry(a, 3, 0), Sp, Land, Sp,
            TableEntry(a, 4, 1), Sp, Land, Sp,
            TableEntry(a, 5, 1), Sp, Land, Sp,
            TableEntry(a, 6, 1), Sp, Land, Sp,
            TableEntry(a, 7, 2), Sp, Land, Sp, Nl,
            TableEntry(b, 0, 0), Sp, Land, Sp,
            TableEntry(b, 1, 0), Sp, Land, Sp,
            TableEntry(b, 2, 0), Sp, Land, Sp,
            TableEntry(b, 3, 0), Sp, Land, Sp,
            TableEntry(b, 4, 1), Sp, Land, Sp,
            TableEntry(b, 5, 1), Sp, Land, Sp,
            TableEntry(b, 6, 2), Sp, Land, Sp,
            TableEntry(b, 7, 2), Sp, Land, Sp, Nl,
            Open, Forall, Sp, x, Comma, Sp,
            Apply(a, x), Sp, Eq, Sp, x, Sp, Iff, Sp, x, Sp, Eq, Sp, D(0), Close,
            Sp, Land, Sp,
            Open, Forall, Sp, x, Comma, Sp,
            Apply(b, x), Sp, Eq, Sp, x, Sp, Iff, Sp, x, Sp, Eq, Sp, D(0), Close,
            Sp, Land, Sp, Nl,
            Apply(Seq(Operatorname, Grp(F.Id("card"))), FinEight()),
            Sp, Eq, Sp, D(8), Sp, Land, Sp,
            Apply(F.Id("rankSpectrumValue"), a, D(1)), Sp, Eq, Sp, D(3), Sp,
            Land, Sp,
            Apply(F.Id("rankSpectrumValue"), b, D(1)), Sp, Eq, Sp, D(3),
            Sp, Land, Sp, Nl,
            Open, Forall, Sp, k, Comma, Sp, D(2), Sp, Leq, Sp, k, Sp,
            Rightarrow, Sp, rankA, Sp, Eq, Sp, D(1), Close, Sp, Land, Sp,
            Open, Forall, Sp, k, Comma, Sp, D(2), Sp, Leq, Sp, k, Sp,
            Rightarrow, Sp, rankB, Sp, Eq, Sp, D(1), Close,
            Sp, Land, Sp, Nl,
            Open, Forall, Sp, k, Comma, Sp, traceA, Sp, Eq, Sp, traceB, Close,
            Sp, Land, Sp,
            Open, Forall, Sp, k, Comma, Sp, rankA, Sp, Eq, Sp, rankB, Close,
            Sp, Land, Sp, Nl,
            leavesA, Sp, Eq, Sp, Multiset(3, 1, 0), Sp, Land, Sp,
            leavesB, Sp, Eq, Sp, Multiset(2, 2, 0), Sp, Land, Sp,
            leavesA, Sp, Neq, Sp, leavesB, Sp, Land, Sp, Nl,
            Neg, Sp, Exists, Sp, F.Id("e"), Colon, Sp, equivPerm, Comma, Esc,
            Apply(Seq(Operatorname, Grp(F.Id("Semiconj"))), F.Id("e"), a, b), Dot));
    }
}
