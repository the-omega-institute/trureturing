using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class SpechtOrdinaryTraceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral ordinary traces of literal same-partition Specht modules",
        H("Integral ordinary Specht traces"),
        Blocks(
            Paragraph(Text("This source is part of the natively compiled full ordinary HSW consumer. The selected public supplier is TauCeti at revision 5a01f5fe3621126cccf9ba22e700493cbc7b7156; the repository pins are unchanged. The unfinished escape audit is issue 24542.")),
            Paragraph(Text("The rational trace is an algebraic integer by the pinned Mathlib theorem FDRep.isIntegral_character, hence an integer. Its numerator therefore casts back exactly. Finite scalar extension carries the rational trace to the complex trace. The existing D5 class-function descent and the full permutation partition give the integer value on a conjugacy class, including every fixed point. The independently constructed complex representation is the existing scalar extension of the polytabloid span for the literal YoungDiagram.ofPartition of the same partition.")),
            Describe.Lean(DescribeId.Create("ordinary-trace-certification"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtOrdinaryTrace.spechtCharValue_ordinaryTrace"),
                H("Same-partition ordinary trace certification"),
                StatementSource.FromAuthor(Certification()), AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026spechtpolytabloids")),
                Blocks(Paragraph(Text("SpechtComplex(mu) denotes exactly TauCeti.spechtModuleℂ mu, with its existing action rho; parts(partition(sigma)) means the full permutation partition, including parts equal to one. Simple is the categorical simplicity of that finite-dimensional representation. The trace is LinearMap.trace over Complex of that action, and intCast is the integer-to-complex cast. The statement includes existence of a representative and equality at every representative. Its two conclusions certify the original irreducibility and trace obligations; integrality itself does not require simplicity. This bind-only source composition is a necessary semantic certification endpoint, with no independent admission claim."))),
                DescribeRole.Theorem),
            Paragraph(Text("SpechtThreeRowCauchy identifies the exact three-variable HSW.frobChar coefficient with this independently constructed same-shape ordinary trace through the mixed pairing and finite Cauchy Gram delta. Its two evaluated consumers retain literal positive parts and zero padding, full cycle partitions, both original weighted sums, reciprocal centralizer factors and the parity-dependent binomial value. The original full assertion is already preregistered in issue 21960; the coefficient audit 22528 does not close it.")))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? Seq(Operatorname, Grp(Id(name)))
        : new Formula.Apply(Seq(Operatorname, Grp(Id(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Seq(Open, a, Close), FormulaLogicOperator.And, Seq(Open, b, Close));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Seq(Open, a, Close), FormulaLogicOperator.Implies, Seq(Open, b, Close));
    private static Formula Certification()
    {
        Formula n = Id("n"), mu = Id("mu"), nu = Id("nu"), sigma = Id("sigma"), tau = Id("tau");
        Formula perm = Call("Perm", Call("Fin", n)), shape = Call("Partition", n);
        Formula module = Call("SpechtComplex", mu);
        Formula HasParts(Formula g) => Eq(Call("parts", Call("partition", g)), Call("parts", nu));
        Formula trace = Eq(Call("trace", Call("Complex"), Call("rho", module, tau)),
            Call("intCast", Call("spechtCharValue", mu, nu)));
        Formula every = All("tau", perm, Imp(HasParts(tau), trace));
        Formula witness = Exists("sigma", perm, And(HasParts(sigma), every));
        return Disp(All("n", Call("Nat"), All("mu", shape, All("nu", shape,
            And(Call("Simple", module), witness)))));
    }
}
