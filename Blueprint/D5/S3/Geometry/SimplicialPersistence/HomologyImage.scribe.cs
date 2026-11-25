using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.SimplicialPersistence;

internal sealed class HomologyImageDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/SimplicialPersistence/HomologyImage.";
    private const string Reference = "memoliwanwang2022persistentlaplacians";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite real harmonic representatives of an actual induced homology image.",
        H("Harmonic representatives and homology images"),
        Blocks(
            Node("weighted-module", "WeightedModule", "Real chains with positive weights",
                "Let I be any finite type, M any abelian group with a specified integer module structure, "
                + "a an integer basis of M indexed by I, and w:I→Real any function with w(i)>0 for every i. "
                + "WeightedModule is Real tensor over Integer with M. Its coefficient equivalence is the "
                + "base change of a. Dividing each coefficient by sqrt(w(i)) identifies it with the ordinary "
                + "Euclidean space on I and induces its norm and inner product. Empty I is included.",
                DescribeRole.Definition),
            Node("weighted-inner", "weighted_inner", "The exact reciprocal-weight metric",
                "For every I, M, a and positive w as above and every pair of real chains x,y, "
                + "inner(x,y) = sum over i in I of coefficient(x,i) coefficient(y,i) / w(i). "
                + "The weights may be arbitrary positive reals. The statement assumes no common positive "
                + "lower bound or upper bound. The inner product is obtained by pulling back Euclidean "
                + "coordinates, so every subsequent adjoint uses this metric.", DescribeRole.Theorem),
            Node("cycle-class", "cycleClass", "Genuine categorical homology classes",
                "For every short complex A→B→C of real modules, cycleClass is the canonical map from "
                + "the kernel of B→C to Mathlib's actual categorical homology. It uses moduleCatCyclesIso "
                + "and homologyπ. Its kernel consists precisely of incoming boundaries. For a map of short "
                + "complexes, cycleMap restricts the actual middle chain map to the cycle kernels, and "
                + "imageClass takes its target homology class. Naturality identifies its range with the "
                + "range of the actual induced ShortComplex.homologyMap.", DescribeRole.Definition),
            Node("filling-domain", "FillingDomain", "All admissible incoming chains",
                "For a map φ from A→B→C to X→Y→Z, FillingDomain is {u in X | b(u) lies in range(i)}, "
                + "where b:X→Y is the target incoming boundary and i:B→Y is the middle component of φ. "
                + "It is a linear inverse image, so cancellation among arbitrary linear combinations "
                + "is retained. When i is injective, restrictedBoundary T sends u to the unique vector "
                + "of B with i(T(u))=b(u). The metric on its domain is inherited from X.",
                DescribeRole.Definition),
            Node("laplacian", "laplacian", "The persistent operator",
                "Take abelian real modules A,Y,Z and finite real inner product spaces B,C,X. Let "
                + "f:A→B, d:B→C, b:X→Y and e:Y→Z be linear, with d f=0 and e b=0. Let φ be any "
                + "commuting map of these two short complexes whose middle component i is injective. "
                + "With T the restricted incoming boundary, the operator on B is Delta = T T* + d* d. "
                + "The star denotes the adjoint for the given metrics, including the inherited domain metric.",
                DescribeRole.Definition),
            Node("kernel", "laplacian_eq_zero", "The energy criterion",
                "For every choice of the six real modules, metrics, four differentials and commuting "
                + "short-complex map described above, every proof that its middle component is injective, "
                + "and every x in B, Delta(x)=0 if and only if T*(x)=0 and d(x)=0. The sum of the squared "
                + "norms of these two vectors equals inner(Delta(x),x). Positivity gives both vanishing "
                + "conditions even when the spaces or differentials have rank zero.", DescribeRole.Theorem),
            Node("equivalence", "harmonicEquivImage", "Canonical harmonic representatives",
                "In addition assume that φ's component C→Z is injective. Restricted incoming boundaries "
                + "then lie in ker(d), and their image in this cycle space is exactly ker(imageClass). "
                + "Orthogonal decomposition of cycles modulo that kernel constructs a real linear "
                + "equivalence from ker(Delta) to range(ShortComplex.homologyMap φ). The quotient and "
                + "orthogonal-complement equivalences are the existing finite-dimensional Mathlib results.",
                DescribeRole.Definition),
            Node("equivalence-formula", "harmonicEquivImage_apply", "The included representative",
                "For all the same data, both injectivity proofs, and every x in ker(Delta), the value "
                + "of harmonicEquivImage at x, regarded as a target homology class, equals cycleClass "
                + "of cycleMap applied to the underlying cycle x. Thus the equivalence sends a harmonic "
                + "vector to the class of its actual included chain.", DescribeRole.Theorem),
            Node("natural-complex", "realComplex", "Every natural degree and the zero differential",
                "Let P(n) be a finite real inner product space for every natural n, with linear maps "
                + "d(n):P(n+1)→P(n) satisfying d(n)d(n+1)=0 for every n. realComplex is the actual full "
                + "Mathlib chain complex with these terms. outgoing is zero at n=0 and d(n) at degree "
                + "n+1. window computes its ordinary homology in degree q using the incoming map d(q) "
                + "and this outgoing differential. windowIso compares it to the actual chain complex's "
                + "short complex; it includes q=0. No truncation index is introduced.", DescribeRole.Definition),
            Node("natural-equivalence", "naturalHodgeEquiv", "The actual full-complex image",
                "Let Q(n), b(n) be a second such family, and i(n):P(n)→Q(n) injective linear maps in "
                + "every natural degree, commuting with the successive differentials. For every natural q, "
                + "naturalHodgeEquiv is a real linear equivalence from the kernel of the corresponding "
                + "persistent Laplacian to range(HomologicalComplex.homologyMap(realChainMap i,q)). "
                + "Homology naturality across windowIso transports the short-complex equivalence to "
                + "this actual homology map.", DescribeRole.Definition),
            Node("natural-cycle", "naturalHodge_cycle", "Harmonic chains are ordinary cycles",
                "For every pair of natural-degree families P,Q, square-zero boundary families d,b and "
                + "commuting injective family i as above, every natural q and every harmonic q-chain x, "
                + "outgoing(d,q)(x)=0. At q=0 this is the unaugmented zero differential.", DescribeRole.Theorem),
            Node("natural-formula", "naturalHodgeEquiv_apply", "The actual homology-class formula",
                "For every such full family and every degree q and harmonic chain x, "
                + "naturalHodgeEquiv(x), regarded in target homology, equals includedClass(x). "
                + "includedClass takes the actual included cycle, forms its ordinary short-complex "
                + "homology class and applies the inverse of the canonical homology comparison. "
                + "This is the class [i(q)(x)] in the actual target chain-complex homology.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
        DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromLiterature(Reference), Blocks(Paragraph(Text(prose))), role);
}
