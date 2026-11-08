using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class FlatPairJointBlocksDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Circle and quaternionic action tables on a complete frame of the original real metric space.",
        H("Joint Blocks of a Flat Skew Pair"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("original-space-flat-pair-joint-blocks"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/FlatPairJointBlocks.HasFlatPairJointBlocks"),
                H("Complete original-space frames"),
                StatementSource.FromAuthor(FrameFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "F is an arbitrary finite-dimensional real inner-product space, with its given " +
                        "positive metric. A and D are endomorphisms of this same F. The frame b is an " +
                        "orthonormal basis indexed by the disjoint union of Fin c times Fin 2 and " +
                        "Fin h times Fin 4. Thus it spans every original vector and makes distinct blocks " +
                        "orthogonal. Both c and h may be zero. The arrays a,d are arbitrary real functions " +
                        "on Fin c; lambda,t are real functions on Fin h. No equality of parameters between " +
                        "different blocks is imposed.")),
                    Paragraph(Text(
                        "C means that, for every circle index i, a(i)^2+d(i)^2=1. Writing the two " +
                        "original basis vectors as q,r, the four required equations are " +
                        "Aq=a(i)r, Ar=-a(i)q, Dq=d(i)r, Dr=-d(i)q. The operator J on their plane " +
                        "sends q to r and r to -q, so J is skew and J squared is minus the identity.")),
                    Paragraph(Text(
                        "Q means that, for every quaternionic index j, 0<lambda(j)<1 and -1<t(j)<1. " +
                        "Write alpha=sqrt(lambda(j)), delta=sqrt(1-lambda(j)), " +
                        "s=sqrt(1-t(j)^2), and write its four original vectors as q,r,u,z. " +
                        "The A table is Aq=alpha r, Ar=-alpha q, Au=alpha z, Az=-alpha u. " +
                        "The D table is Dq=delta(t r+s u), Dr=delta(-t q-s z), " +
                        "Du=delta(t z-s q), Dz=delta(-t u+s r). These are all eight equations, " +
                        "with independently chosen lambda and t for every block.")),
                    Paragraph(Text(
                        "The order q,r,u,z corresponds to q,Jone q,Jtwo q,Jone Jtwo q. " +
                        "Jone has table r,-q,z,-u and Jtwo has table u,-z,-q,r. " +
                        "Their squares are minus the identity and they anticommute. Both tables are " +
                        "skew with respect to the original metric. The displayed action equations make " +
                        "each plane or four-dimensional span jointly invariant under the given A,D. " +
                        "This condition specifies a full frame; it does not assert its existence for " +
                        "an arbitrary pair."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("flat-pair-complete-joint-block-classification"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/FlatPairJointBlocks.flat_pair_joint_blocks_iff"),
                H("Complete classification and converse"),
                StatementSource.FromAuthor(ClassificationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Skew(T) means inner(Tx,y)=-inner(x,Ty) for all original vectors x,y in F. " +
                    "Flat(A,D) means -A squared-D squared is the identity endomorphism of F. " +
                    "The left side is precisely the complete original-space frame condition defined above. " +
                    "The equivalence includes the zero space, all zero residual complements, both endpoint " +
                    "square shares, both collinear signs, the strict interior, independent block parameters, " +
                    "and the converse for every complete permitted assembly. No uniqueness is asserted.")))),
            Paragraph(Text("Square and mixed spectral coordinates")),
            Paragraph(Text(
                "For skew A,D with -A squared-D squared=I, put P=-A squared and " +
                "S=-(AD+DA)/2. Skewness makes P and S symmetric. The identity P=I+D squared " +
                "makes P commute with D; its definition makes it commute with A. The same square " +
                "relations make S commute with both A and D, hence with P. The existing " +
                "Commute.isSymmetric_directSumDecomposition supplies the simultaneous symmetric " +
                "decomposition into intersections of their eigenspaces. These are subspaces of " +
                "the original F, and commutation makes them invariant under the original maps.")),
            Paragraph(Text(
                "On a nonzero joint eigenspace P=lambda I and S=sigma I, skewness gives " +
                "the squared norms of Ax and Dx as lambda and 1-lambda times the squared norm " +
                "of x. Therefore 0<=lambda<=1. At lambda=0 the original A vanishes; at lambda=1 " +
                "the original D vanishes. These cases require circle planes, including a zero " +
                "residual space after their removal. For 0<lambda<1, put Jone=A/sqrt(lambda), " +
                "J=D/sqrt(1-lambda), and t=sigma/(sqrt(lambda)sqrt(1-lambda)). " +
                "Both normalized maps are skew complex structures. Cauchy-Schwarz gives " +
                "-1<=t<=1. At t=1 or t=-1 the norm of (J-t Jone)x vanishes, giving " +
                "J=t Jone and again a circle plane.")),
            Paragraph(Text("Metric orbit and complement exhaustion")),
            Paragraph(Text(
                "In the strict interior define Jtwo=(J-t Jone)/sqrt(1-t squared). " +
                "Expanding with Jone J+J Jone=-2t I gives Jtwo squared=-I and " +
                "Jone Jtwo=-Jtwo Jone. The four vectors q,Jone q,Jtwo q,Jone Jtwo q " +
                "are orthonormal whenever q is unit: each normalized map preserves the inner " +
                "product, and the diagonal pairings of the three skew maps Jone,Jtwo,Jone Jtwo " +
                "vanish. The two multiplication tables above show joint invariance of their span. " +
                "For any jointly invariant span V, skewness gives inner(y,Ax)=-inner(Ay,x)=0 " +
                "for y in V and x in its orthogonal complement, and likewise for D. Thus the " +
                "actual restrictions to V orthogonal inherit skewness and the flat identity. " +
                "Removing a nonzero two- or four-vector orbit strictly reduces the finite " +
                "dimension. Repeating this construction is the required exhaustion step; a " +
                "single spectral fibre or a single orbit does not describe the whole space.")),
            Paragraph(Text("Converse arithmetic")),
            Paragraph(Text(
                "On a circle plane the two negative squares sum to (a squared+d squared)I=I. " +
                "On a quaternionic block, the square of t Jone+s Jtwo is " +
                "-(t squared+s squared)I=-I because the mixed terms cancel. Hence the two " +
                "negative squares are lambda I and (1-lambda)I. Equality on every vector of a " +
                "complete basis gives the same identity on F. The zero space satisfies it too. " +
                "No uniqueness of block order, multiplicity, or parameters is asserted.")),
            Paragraph(Text("Original-space branch restrictions")),
            Paragraph(Text(
                "Let e be unit in the original W, let K,L be skew, and suppose " +
                "-K squared-L squared=I+beta P(e), where P(e)x=inner(e,x)e. " +
                "A complete flat-pair classification would apply directly to W when beta=0. " +
                "Its frame would give dim W=2c+4h and therefore even dimension.")),
            Paragraph(Text(
                "When beta=-1, pairing the square identity with e gives " +
                "the sum of the squared norms of Ke and Le equal to zero. Both vectors vanish. " +
                "Skewness then preserves the original line through e and its actual orthogonal " +
                "complement. On that complement P(e) vanishes, so the restricted original K,L " +
                "satisfy the flat identity. This includes a zero complement. A flat frame there " +
                "can be adjoined to the original fixed vector e.")),
            Paragraph(Text(
                "For beta=1 the following implication is conditional on an explicit original core: " +
                "v=Ke,w=Le are orthonormal, Kv=-e,Kw=0,Lv=0,Lw=-e. Skewness gives " +
                "inner(e,v)=inner(e,w)=0. The six equations make the original " +
                "U=span(e,v,w) invariant. The skew-pair complement argument derives invariance " +
                "of the original U orthogonal; it is not an additional premise. Since e belongs " +
                "to U, P(e) vanishes there, and restricting the original square identity derives " +
                "flatness of the actual restrictions. A flat frame of that complement, including " +
                "the zero complement, can then be adjoined to the original triple.")),
            Paragraph(Text(
                "Conversely, on the same original W an orthogonal assembly of flat blocks gives I. " +
                "Adjoining a fixed unit line gives I-P(e). Adjoining the stated orthonormal triple " +
                "gives I+P(e), since the core negative-square sum sends e to 2e and sends v,w " +
                "to themselves. These ambient identities follow by linearity on the respective " +
                "spanning original vectors. They require a complete flat frame on the complement.")),
            Paragraph(Text(
                "The exhaustion of beta by zero, minus one and plus one, and the derivation of " +
                "the positive core from beta=1 alone, are additional assertions. The conditional " +
                "positive implication above does not establish either of them. It gives no " +
                "cyclicity, full Lie generation, non-scalar selection, physical interpretation, " +
                "amplitude-algebra identification, or elimination of side blocks.")))));

    private static Formula Call(string name, params Formula[] args)
    {
        var parts = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) parts.Add(Comma);
            parts.Add(args[i]);
        }
        parts.Add(Close);
        return Seq([.. parts]);
    }

    private static Formula ClassificationFormula() => Disp(Seq(
        Forall, Sp, F.Id("F"), Colon, F.Id("Type"), Comma,
        OpenBracket, Call("NormedAddCommGroup", F.Id("F")), CloseBracket,
        OpenBracket, Call("InnerProductSpace", Seq(Mathbb, Grp(F.Id("R"))), F.Id("F")), CloseBracket,
        OpenBracket, Call("FiniteDimensional", Seq(Mathbb, Grp(F.Id("R"))), F.Id("F")), CloseBracket, Comma,
        Forall, Sp, F.Id("A"), Comma, F.Id("D"), Colon, Call("End", Seq(Mathbb, Grp(F.Id("R"))), F.Id("F")), Comma,
        Call("HasFlatPairJointBlocks", F.Id("A"), F.Id("D")), Iff,
        Call("Skew", F.Id("A")), Land, Sp, Call("Skew", F.Id("D")), Land, Sp,
        Call("Flat", F.Id("A"), F.Id("D")), Dot));

    private static Formula FrameFormula() => Disp(Seq(
        Forall, Sp, F.Id("F"), Colon, F.Id("Type"), Comma,
        OpenBracket, Call("NormedAddCommGroup", F.Id("F")), CloseBracket,
        OpenBracket, Call("InnerProductSpace", Seq(Mathbb, Grp(F.Id("R"))), F.Id("F")), CloseBracket,
        OpenBracket, Call("FiniteDimensional", Seq(Mathbb, Grp(F.Id("R"))), F.Id("F")), CloseBracket, Comma,
        Forall, Sp, F.Id("A"), Comma, F.Id("D"), Colon, Call("End", Seq(Mathbb, Grp(F.Id("R"))), F.Id("F")), Comma,
        Call("HasFlatPairJointBlocks", F.Id("A"), F.Id("D")), Iff,
        Exists, Sp, F.Id("c"), Comma, F.Id("h"), Colon, Seq(Mathbb, Grp(F.Id("N"))), Comma,
        Exists, Sp, F.Id("b"), Colon, Call("Frame", F.Id("F"), F.Id("c"), F.Id("h")), Comma,
        Exists, Sp, F.Id("a"), Comma, F.Id("d"), Colon, Call("Fin", F.Id("c")), To, Sp, Seq(Mathbb, Grp(F.Id("R"))), Comma,
        Exists, Sp, LambdaLower, Comma, F.Id("t"), Colon, Call("Fin", F.Id("h")), To, Sp, Seq(Mathbb, Grp(F.Id("R"))), Comma,
        Call("C", F.Id("A"), F.Id("D"), F.Id("b"), F.Id("a"), F.Id("d")), Land, Sp,
        Call("Q", F.Id("A"), F.Id("D"), F.Id("b"), LambdaLower, F.Id("t")), Dot));
}
