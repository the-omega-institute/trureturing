using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.FourierFibers;

internal sealed class FiniteObservabilityKrylovCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite time window is faithful exactly when its existing observable "
            + "Krylov space fills the carrier.",
        H("Finite Observability Krylov Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-hidden-kernel-trivial-iff-observable-krylov-top"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/FourierFibers/FiniteObservabilityKrylovCriterion.finite_hidden_kernel_trivial_iff_observable_krylov_top"),
                H("Trivial hidden kernel equals full Krylov span"),
                StatementSource.FromAuthor(KrylovFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The finite common kernel of all delayed readouts is trivial exactly when the observable Krylov subspace is the whole finite-dimensional carrier.")),
                    Paragraph(Text(
                        "This node reuses Trueturning's frozen orthogonal-duality theorem and Mathlib's orthogonal-complement criterion instead of introducing a parallel observability theory."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula KrylovFormula()
    {
        Formula evolution = F.Id("E");
        Formula readout = F.Id("r");
        Formula depth = F.Id("d");
        Formula time = F.Id("t");
        Formula inf = new Formula.Subscript(
            Seq(Operatorname, Grp(F.Id("inf"))),
            Seq(time, Sp, Le, Sp, depth));
        Formula kernel = Call("ker",
            Seq(readout, Sp, Circ, Sp, evolution, Caret, Grp(time)));
        return Disp(Seq(
            Forall, Sp, evolution, Comma, Sp, readout, Comma, Sp, depth,
            Comma, Sp,
            inf, Sp, kernel, Sp, Eq, Sp, F.Id("bot"),
            Sp, Iff, Sp,
            Call("observableKrylov", evolution, readout, depth),
            Sp, Eq, Sp, F.Id("top"), Dot));
    }

}
