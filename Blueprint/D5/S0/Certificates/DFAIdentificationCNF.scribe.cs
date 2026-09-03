using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class DFAIdentificationCNFDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Certified CNF encodings separate untrusted formula generation "
            + "from sound and complete identification semantics.",
        H("Certified CNF Semantics for DFA Identification"),
        Blocks(Describe.Lean(
            DescribeId.Create("identification-formula-satisfiable-iff"),
            DeclarationHandle.Create(
                "D5/S0/Certificates/DFAIdentificationCNF.identification_formula_satisfiable_iff"),
            H("Formula satisfiability is equivalent to a valid identification"),
            StatementSource.FromAuthor(SatisfiabilityFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The CNF bytes and solver are allowed to be untrusted. Admission requires separate proofs that every satisfying valuation decodes to a valid identification and that every valid identification induces a satisfying valuation.")),
                Paragraph(Text(
                    "This file freezes the proof-carrying interface. An optimized concrete APTA encoder remains an instance obligation and cannot inherit correctness merely from its implementation."))),
            DescribeRole.Theorem)),
        []));

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

    private static Formula SatisfiabilityFormula() => Disp(Seq(
        Call("Satisfiable", Call("formula", F.Id("E"))),
        Sp, Iff, Sp,
        Call("Nonempty", Call("Identification", F.Id("S"), F.Id("B"), F.Id("C")))));
}
