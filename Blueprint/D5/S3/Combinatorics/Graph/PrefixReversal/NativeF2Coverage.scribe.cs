using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeF2CoverageDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeF2Coverage.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every actual configuration in the independently defined two-label insertion layer belongs to the concrete F2 supplier union, and conversely.",
        H("Actual F2 Coverage of the Independent Insertion Layer"),
        Blocks(
            Paragraph(Text(
                "The base circle is the identity tuple with labels zero and m erased. "
                + "Layer({0,m},P) is specified before any walk: erasing those two labels "
                + "from the actual configuration must give P or its reverse. F2Domain "
                + "is the previously defined two-star CoreDomain and the complete stars "
                + "at every tuple (1,...,j+1,m,j+2,...,m-1,0), j in Fin(m-2).")),
            Describe.Lean(DescribeId.Create("native-f2-layer-iff"),
                DeclarationHandle.Create(Prefix + "native_f2_layer_iff"),
                H("Concrete F2 Suppliers Exhaust the Independent Layer"),
                StatementSource.FromAuthor(CoverageFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every m at least four and every actual permutation v, F2Domain(m,v) "
                        + "holds exactly when v belongs to the independently specified two-label "
                        + "insertion layer over the erased identity circle. This closes the "
                        + "coverage gap between the finite graft construction and the insertion "
                        + "layer; no support definition or configuration search is assumed.")),
                    Paragraph(Text(
                        "Write B=(1,...,m-1). The generic childDomain_exists theorem orients "
                        + "the actual residual after deleting zero so that deleting m gives B. "
                        + "The existing cyclic gap fiber theorem then gives a unique gap "
                        + "r in Fin(m-1), with residual circle (m,B.rotate(r)).")),
                    Paragraph(Text(
                        "Gap zero is the lower shadow supplier: rotating its actual residual "
                        + "by m-2 gives (m,B). Every positive gap r is the concrete contact "
                        + "j=r-1: rotating that residual by j+1 gives (m,B.rotate(j+1)). "
                        + "These exhaust all oriented children and hence cover every actual "
                        + "configuration, including the negatively oriented case supplied by "
                        + "the generic insertion-layer theorem.")),
                    Paragraph(Text(
                        "Conversely, deleting m from each of these residuals gives B. The "
                        + "upper supplier is the image of the lower residual under swapping "
                        + "zero and m; this swap fixes every label of B, so deleting zero "
                        + "from its residual also gives B. Both core stars and every contact "
                        + "star therefore lie wholly inside the independent two-label layer."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "Combining this equality of independently specified domains with the existing "
                + "finite F2 Hamilton-cycle construction identifies its spanning domain. "
                + "The later marked-path recombination and recursive Hamiltonicity of the "
                + "entire native graph require their separate proofs.")))));

    private static Formula CoverageFormula()
    {
        Formula m = F.Id("m"), v = F.Id("v");
        Formula selected = Call("FinsetPair", D(0), Call("FinLast", m));
        Formula parent = Call("erase", selected, Call("configurationCycle", Call("identity", m)));
        Formula assertion = new Formula.Logic(Call("F2Domain", m, v), FormulaLogicOperator.Iff,
            Call("Layer", selected, parent, v));
        return Disp(All("m", Call("Nat"), Implies(Le(D(4), m),
            All("v", Call("Configuration", m), assertion))));
    }

    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
            : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
