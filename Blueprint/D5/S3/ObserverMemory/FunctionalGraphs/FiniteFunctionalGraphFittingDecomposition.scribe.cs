using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.FunctionalGraphs;

internal sealed class FiniteFunctionalGraphFittingDecompositionDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite self-map transfer decomposes into a nilpotent transient part and its periodic core.",
        H("Finite Functional-Graph Fitting Decomposition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-functional-graph-fitting-decomposition"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/FunctionalGraphs/"
                        + "FiniteFunctionalGraphFittingDecomposition."
                        + "finite_functional_graph_fitting_decomposition"),
                H("The transfer splits into transient and periodic summands"),
                StatementSource.FromAuthor(DecompositionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let tau be a self-map of a finite state carrier Y. The transfer operator "
                            + "sends the canonical basis vector at y to the basis vector at tau(y). "
                            + "Let N be any natural exponent whose iterate image is exactly the "
                            + "periodic-point set.")),
                    Paragraph(Text(
                        "The transient subspace is constructed independently as the kernel of "
                            + "coefficient aggregation along the N-th iterate of tau. "
                            + "The theorem identifies it with the kernel of the corresponding "
                            + "transfer power before proving nilpotence of the restricted transfer.")),
                    Paragraph(Text(
                        "The canonical linearEquivFunOnFinite map identifies finite-support "
                            + "vectors with the source carrier C^Y. A public intertwining clause "
                            + "shows that transferOperator agrees through this equivalence with "
                            + "Mathlib's function-space linearMap induced directly by tau.")),
                    Paragraph(Text(
                        "The periodic-core subspace is the span of the canonical basis vectors at "
                            + "periodic points. The update induces the displayed canonical "
                            + "permutation of those points, and the restricted transfer acts on "
                            + "every periodic basis vector through exactly that permutation.")),
                    Paragraph(Text(
                        "Repository search supplied the canonical transfer, periodic-core, and "
                            + "stable-image declarations but no theorem packaging all seven clauses. "
                            + "Pinned Mathlib supplies Finsupp range, finite-dimensional "
                            + "rank-nullity and complement criteria, iterated injectivity, the "
                            + "injective-surjective equivalence, and the periodic-point bijection "
                            + "applied directly by the proof."))),
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

    private static Formula DecompositionFormula()
    {
        Formula carrier = F.Id("Y"), update = Tau, point = F.Id("p");
        Formula exponent = F.Id("N");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula iterate = Seq(update, Caret, Grp(exponent));
        Formula transfer = Apply(F.Id("transferOperator"), update);
        Formula power = Seq(transfer, Caret, Grp(exponent));
        Formula kernel = Seq(Ker, Sp, power);
        Formula range = Apply(Seq(Operatorname, Grp(F.Id("range"))), power);
        Formula stableImage = Apply(Seq(Operatorname, Grp(F.Id("range"))), iterate);
        Formula periodicSet = Apply(Seq(Operatorname, Grp(F.Id("periodicPts"))), update);
        Formula transient = Apply(F.Id("transientSubspace"), update, exponent);
        Formula transientMap = Apply(F.Id("transientTransfer"), update, exponent);
        Formula core = Apply(F.Id("periodicCoreSubspace"), update);
        Formula coreMap = Apply(F.Id("periodicCoreTransfer"), update);
        Formula periodicPoints = Apply(F.Id("PeriodicCore"), update);
        Formula permutation = Apply(F.Id("periodicCorePermutation"), update, point);
        Formula basis = Apply(F.Id("periodicBasisVector"), update, point);
        Formula permutedBasis = Apply(F.Id("periodicBasisVector"), update, permutation);
        Formula vector = F.Id("v");
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula vectorType = Apply(F.Id("Finsupp"), carrier, complex);
        Formula bridge = Apply(
            F.Id("linearEquivFunOnFinite"), complex, complex, carrier);
        Formula functionTransfer = Apply(F.Id("linearMap"), complex, complex, update);

        return Disp(Seq(
            Forall, Sp, carrier, Comma, Sp,
            Operatorname, Grp(F.Id("Finite")), Open, carrier, Close, Comma, RowBreak,
            Forall, Sp, update, Colon, Sp, carrier, Sp, To, Sp, carrier, Comma, RowBreak,
            Forall, Sp, exponent, Sp, InMacro, Sp, naturals, Comma, RowBreak,
            stableImage, Sp, Eq, Sp, periodicSet, Sp, Rightarrow, Sp, Open,
                Apply(F.Id("IsCompl"), kernel, range), Sp, Land, RowBreak,
                transient, Sp, Eq, Sp, kernel, Sp, Land, RowBreak,
                Apply(F.Id("IsNilpotent"), transientMap), Sp, Land, RowBreak,
                range, Sp, Eq, Sp, core, Sp, Land, RowBreak,
                Apply(F.Id("Bijective"), coreMap), Sp, Land, RowBreak,
                Open, Forall, Sp, point, Colon, Sp, periodicPoints, Comma, Sp,
                    Apply(coreMap, basis), Sp, Eq, Sp, permutedBasis, Close,
                Sp, Land, RowBreak,
                Open, Forall, Sp, vector, Colon, Sp, vectorType, Comma, Sp,
                    Apply(bridge, Apply(transfer, vector)), Sp, Eq, Sp,
                    Apply(functionTransfer, Apply(bridge, vector)), Close,
            Close, Dot));
    }
}
