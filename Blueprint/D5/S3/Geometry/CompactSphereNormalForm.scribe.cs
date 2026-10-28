using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class CompactSphereNormalFormDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/CompactSphereNormalForm.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compact sphere-coproduct source models admit actual finite positive sphere-list models.",
        H("Compact sphere source normal form"),
        Blocks(
            Node("dimension", "PositiveDimension", "Strictly positive sphere dimensions",
                "An output dimension is a natural number together with its strict positivity proof. Zero-dimensional spheres are accounted for by separate point components.", DescribeRole.Definition),
            Node("bouquet", "Bouquet", "The actual coordinate-based quotient bouquet",
                "For a finite list l of positive dimensions, use CompactWedgeFiniteFactor.FamilyWedge with indices Fin(l.length), factors EuclideanSphereJoin.StdSphere of dimension (l.get i).val, and coordinatePoint basepoints. The empty list has the additional distinguished representative and is exactly a one-point space. Multiplicities in the list are retained.", DescribeRole.Definition),
            Node("model", "Model", "The finite outer sigma model",
                "For m natural and b:Fin m to lists of positive dimensions, Model b is the topological dependent coproduct of Bouquet(b k). It is empty when m=0. An empty inner list gives a point component rather than an absent component.", DescribeRole.Definition),
            Node("transport", "HomotopyModel", "Output data include the actual homotopy equivalence",
                "For a topological space X, the data are size m, lists b:Fin m to List PositiveDimension, and an actual X homotopy equivalent to Model b. This packages continuous maps and both inverse homotopies, not just an existential classification predicate or an assumed finite endpoint.", DescribeRole.Definition),
            Node("list", "dimensionList", "Dependent finite enumeration of a positive family",
                "For any finite type J with a Fintype instance and dimension function n:J to PositiveDimension, enumerate J using Fintype.equivFin and List.ofFn. The list keeps every factor, including repeated dimensions. List.get at the induced finite index recovers the original dimension exactly.", DescribeRole.Definition),
            Node("pointed-enumeration", "positiveListHomeomorph", "Pointed quotient homeomorphism to the list",
                "Reindex the actual sigma of spheres along the finite enumeration, casting each sphere only along the proved equality of its natural dimension. Such casts send coordinatePoint to coordinatePoint. The raw map is the identity on the additional Unit summand and the sphere reindexing on the other summand. Both the equality relation and membership in the entire collapsed basepoint subset are preserved and reflected. Apply Mathlib Homeomorph.Quotient.congr to obtain the quotient homeomorphism, bundled with its exact action on the common basepoint. Continuity and openness of sigma maps come from Mathlib; no new compact-factor engine or reflection proof is used.", DescribeRole.Definition),
            Node("finite-coproduct", "finiteCoproductHomeomorph", "Normalize and enumerate the selected finite sphere families",
                "For finite outer A and finite dependent inner families I(a), begin with SphereWedgePositiveNormalization.coproductNormalizationHomeomorph, allowing arbitrary original sphere basepoints q(a,j). Its positive bouquet in each original block is transported to a finite list by positiveListHomeomorph. Each zero-sphere index becomes one copy of the empty-list bouquet via the unique point homeomorphism. Reassemble by Equiv.sumSigmaDistrib over C=A plus Sigma a ZeroIndex(d a), then enumerate C by Fin(card C). In particular each original block contributes its positive bouquet even when its positive list is empty; each S0 factor contributes an additional isolated point; empty A stays empty. The result is an actual homeomorphism with no factor discarded.", DescribeRole.Definition),
            Node("empty", "emptyModel", "The empty source uses no outer summands",
                "For an empty topological source X, the output has size zero and the unique empty family of lists. Use the actual homeomorphism between empty spaces and its induced homotopy equivalence. This branch does not replace the empty space by a point.", DescribeRole.Definition),
            Node("nonempty", "nonemptyCompactModel", "Compact nonempty arbitrary source transport",
                "Let X be compact and nonempty, with an actual homotopy equivalence to an arbitrary dependent coproduct of ordinary pointed sphere wedges. Neither original index type is required to be finite. Apply CompactWedgeFiniteFactor.finiteFactorHomotopyEquiv to obtain its actual finite selected outer and inner families. Then apply finiteCoproductHomeomorph to precisely those unchanged selected spheres and compose the equivalences. The right homotopy is supplied by the existing finite-factor construction and requires no invariant submodel assumption. The output is bundled with a proof that its outer size is positive, obtained from the finite index of the image of a source point.", DescribeRole.Definition),
            Node("compact", "compactModel", "All compact coproduct sources, including the empty branch",
                "For any compact X and actual equivalence to the arbitrary sphere-wedge coproduct, split on source nonemptiness. Use nonemptyCompactModel in the inhabited branch and emptyModel otherwise. Contractibility, S0 factors, empty inner families and arbitrary index families are preserved. No finite-index assumption is imposed on the original source class.", DescribeRole.Definition),
            Node("single-wedge", "compactWedgeModel", "The arbitrary single-wedge source alternative",
                "For a compact X homotopy equivalent to one arbitrary pointed sphere wedge, first use the actual homeomorphism from that wedge to its one-summand dependent coproduct, then apply compactModel. The sphere bases are the supplied original points, and all empty and zero-dimensional inner cases remain in scope.", DescribeRole.Definition),
            Node("contractible", "contractibleModel", "The contractible source alternative",
                "For a ContractibleSpace X, compose Mathlib ContractibleSpace.hequiv_unit with the actual unique-point homeomorphism to the model with size one and empty bouquet list. Compactness is unnecessary for this alternative. These source adapters are intermediate work for the original unsuspended hereditary W conclusion in Carnero Bravo arXiv:2505.06457v2 Question 22. SP means contractible or homotopy equivalent to a wedge of spheres; SW quantifies that property over induced subgraphs. The native carrier maps below identify these actual source models with FiniteComponentClosure normal complexes. HereditaryLexicographicProduct consumes both directions in its final graph composition; these adapter declarations alone assert no graph closure or novelty.", DescribeRole.Definition),
            Node("native-bouquet", "nativeBouquetHomeomorph", "The actual native bouquet and the coordinate sphere quotient",
                "For every finite positive dimension list b, compose FiniteComponentClosure.standardBouquetHomeomorph with a quotient homeomorphism induced by the original spherePointHomeomorph on each sphere and the identity on the additional Unit. The native standardSphereBase is sent exactly to coordinatePoint. Equality and membership in the complete collapsed basepoint subset are preserved and reflected. This identifies the actual quotients; matching names or homotopy classifications are not used as carrier equalities. The empty list retains its one point.", DescribeRole.Definition),
            Node("native-model", "nativeModelHomeomorph", "All finite component carriers, including zero components",
                "For every natural m and family b:Fin m to lists of positive dimensions, apply FiniteComponentClosure.normalHomeomorph and then nativeBouquetHomeomorph in every sigma fiber. This is an actual homeomorphism from the native realization of normalComplex m b to Model b. It includes m=0 and point components. The source-to-native direction supplies the WPlus premises of the real finite closures, and the reverse direction supplies the arbitrary-sphere source-P conclusion of HereditaryLexicographicProduct.result.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
