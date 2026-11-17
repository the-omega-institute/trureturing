using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PascadiOriginalLinearFibersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Physical multiplicities for relevant primitive linear factors in the original prime-cube lattice. A factor direction gives a nonzero step pU with U in the index-p-squared congruence lattice. A fixed linear value has at most 1+6H/(p sigma) actual integer-coordinate preimages in the literal physical box.",
        H("Actual linear-factor fibers"),
        Blocks(
            Paragraph(Text("Fix a prime p, positive X,Y,H with H^2=XY, an oriented basis B of the original lattice p^3 divides w*z-t*u, and a reduced basis B2 of the corresponding index-p^2 lattice with the same integer t,w. Put sigma=sqrt(Q(B2.R)) in the area-preserving weighted metric Q(u,z)=(Y/X)u^2+(X/Y)z^2. The reduced basis is an actual lattice basis with its shortest-vector law; no arbitrary slope lift or assumed counting injection is introduced. The earlier lattice existence theorem supplies this basis when w is a unit modulo p^2.")),
            Describe.Lean(DescribeId.Create("pascadi-relevant-linear-physical-step"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiOriginalLinearFibers.relevant_linear_physical_step"),
                H("A relevant direction descends to the p-squared lattice"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let a,b be coprime integers and w a unit modulo p. If a*B.V.1+b*B.R.1 vanishes modulo p, then the nonzero physical step W=b*B.R+a*B.V equals pU for a nonzero integer vector U satisfying p^2 divides w*U.2-t*U.1.")),
                    Paragraph(Text("The root condition makes W.1 divisible by p. Original lattice membership and the unit w force W.2 to be divisible by p as well. Dividing the original p^3 congruence by p gives the literal p^2 congruence for U. Coprimality and the determinant-p^3 basis rule out W=0."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pascadi-actual-linear-factor-fiber-count"),
                DeclarationHandle.Create("D5/S3/Arith/CharacterSums/PascadiOriginalLinearFibers.actual_linear_factor_fiber_count"),
                H("Actual physical preimages of a fixed linear value"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under those hypotheses, every finite set s of actual integer coordinate vectors z with physical B.R B.V z in the literal X by Y box and with a*z.1-b*z.2 equal to one fixed integer has cardinality at most 1+6H/(p*sigma). The constant is explicit and the shortest length is positive.")),
                    Paragraph(Text("Bezout's identity expresses every coordinate difference in a fixed linear fiber as an integer multiple n of (b,a). Its physical difference is nW. The shortest-vector law and W=pU give Q(W)>=p^2*sigma^2, while two points in the original rectangle have squared distance at most 8XY. Thus |n|<=3H/(p*sigma). The actual coordinate map into these integer parameters is injective by the proved reconstruction identity. Counting the bounded integer interval gives the stated bound."))),
                DescribeRole.Theorem),
            Paragraph(Text("Application boundary: equality of the algebraic values associated to a primitive linear factor must still be connected to the displayed integer linear-value condition. This module bounds a first-point fiber; uniqueness of the second original endpoint from the unit right-side equation remains a separate obligation before using the weight only once in a partner count. The average over original integer (t,w), excluded charts and full six-tuple count are not established here.")))));
}
