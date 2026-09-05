using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.HiddenFlow;

internal sealed class FiniteEditTailDiscontinuityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonconstant Boolean tail observable on a product is continuous nowhere.",
        H("Finite-Edit Tail Discontinuity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a-nonconstant-finite-edit-tail-observable-is-nowhere-continuous"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/HiddenFlow/FiniteEditTailDiscontinuity."
                        + "nonconstant_finite_edit_invariant_nowhere_continuous"),
                H("A nonconstant finite-edit tail observable is nowhere continuous"),
                StatementSource.FromAuthor(TailDiscontinuityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let the coordinate spaces be indexed by the positive natural numbers and "
                            + "give their dependent product the product topology. A Boolean "
                            + "observable is assumed unchanged whenever two inputs differ at only "
                            + "finitely many coordinates.")),
                    Paragraph(Text(
                        "Nonconstancy supplies two inputs with different readings. At any chosen "
                            + "point, continuity into discrete Bool would make its reading constant "
                            + "on a neighborhood. Mathlib's finite piecewise-neighborhood lemma "
                            + "places a finite edit of an input with the other reading inside that "
                            + "neighborhood, giving a contradiction.")),
                    Paragraph(Text(
                        "Repository, pinned-Mathlib, Loogle, and LeanSearch queries found no exact "
                            + "finite-edit discontinuity theorem. The proof reuses "
                            + "exists_finset_piecewise_mem_of_mem_nhds for the product-topology step.")),
                    Paragraph(Text(
                        "The statement records the named topological theorem. Later discussion of "
                            + "particular analytic models and possible stronger topologies is "
                            + "interpretive guidance rather than an additional theorem clause."))),
                DescribeRole.Theorem)),
        []));

    private static Formula TailDiscontinuityFormula()
    {
        Formula positiveNaturals = Seq(
            Mathbb, Grp(F.Id("N")), Underscore, Grp(Gt, D(0)));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula family = F.Id("X");
        Formula index = F.Id("n");
        Formula At(Formula function, Formula argument) =>
            Seq(function, Open, argument, Close);
        Formula fiber = At(family, index);
        Formula product = Seq(
            Prod, Underscore, Grp(index, InMacro, Sp, positiveNaturals), Sp, fiber);
        Formula observable = F.Id("F");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula disagreement = SetOf(
            index, positiveNaturals, NotEqual(At(x, index), At(y, index)));
        Formula invariance = Seq(
            Forall, Sp, x, Comma, Sp, y, Colon, Sp, product, Comma, Sp,
            Call("Finite", disagreement), Sp, Rightarrow, Sp,
            Equal(At(observable, x), At(observable, y)));
        Formula nonconstant = Seq(
            Exists, Sp, a, Comma, Sp, b, Colon, Sp, product, Comma, Sp,
            NotEqual(At(observable, a), At(observable, b)));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, family, Colon, Sp, positiveNaturals, Sp, To, Sp, type, Comma,
            RowBreak, Grp(),
            OpenBracket, Forall, Sp, index, Colon, Sp, positiveNaturals, Comma, Sp,
            Call("TopologicalSpace", fiber), CloseBracket, Comma,
            RowBreak, Grp(),
            observable, Colon, Sp, product, Sp, To, Sp, F.Id("Bool"), Comma,
            RowBreak, Grp(),
            Open, invariance, Close, Sp, Land, Sp,
            Open, nonconstant, Close, Sp, Rightarrow,
            RowBreak, Grp(),
            Forall, Sp, x, Colon, Sp, product, Comma, Sp,
            Neg, Sp, Call("ContinuousAt", observable, x), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula SetOf(Formula element, Formula domain, Formula predicate) =>
        Seq(
            Left, OpenBrace, element, Sp, Colon, Sp, domain,
            Sp, Mid, Sp, predicate, Right, CloseBrace);
}
