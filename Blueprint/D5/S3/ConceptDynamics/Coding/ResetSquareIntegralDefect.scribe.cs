using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class ResetSquareIntegralDefectDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/ResetSquareIntegralDefect.";
    private static Formula I(string name) => F.Id(name);
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Ex(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula M => Call("VertexModule", I("Sign"), I("q"));
    private static Formula L(Formula v) => Call("resetSquareDefect", I("q"), v);
    private static Formula Clock(Formula v) => Call("resetFiveClock", I("q"), v);
    private static Formula Scope(Formula body, bool five, params Formula.BoundVariable[] extra) =>
        All(Imp(five ? Equal(Call("mod", I("q"), Num(4)), Num(2)) : Call("NatPositive", I("q")),
            extra.Length == 0 ? body : All(body, extra)), B("q", I("Nat")));
    private static DocumentBlock Result(string name, string id, string title, Formula statement, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordinary integral kernel and cokernel of squared reset time, with a primitive five-clock.",
        H("Two-step reset arithmetic"),
        Blocks(
            Paragraph(Text("Sign is the original Multiplicative Bool, tau=ofAdd true, and Row=MonoidAlgebra Int Sign. "
                + "VertexModule Sign q is Fin q -> Row. T=transition(resetMatrix q) is the actual integer "
                + "right-row transition: head (sum v) times tau and successor v(j). "
                + "resetSquareDefect=id+T squared, where only T is squared. NatPositive(q) means 0<q. "
                + "Literal coefficients at 1 and tau give rowEquiv: Row equivalent to Int times Int; "
                + "the sum and difference eigenvectors are not an integral basis. "
                + "The abstract period-four normal form is specialized using the original resetFlip and its "
                + "existing involution proof. Every positive length is included.")),
            Result("five_block_classification", "reset-square-five-block", "Constructive five-block arithmetic",
                All(And(Iff(Equal(Call("fiveBlock", I("x")), Num(0)), Equal(I("x"), Num(0))),
                    Iff(Ex(Equal(Call("fiveBlock", I("a")), I("y")), B("a", I("Row"))),
                        Call("Divides", Num(5), Call("add", Call("coeff", I("y"), Num(1)),
                            Call("coeff", I("y"), Call("tau")))))),
                    B("x", I("Row")), B("y", I("Row"))),
                "fiveBlock=3id+2resetFlip has literal matrix [[3,2],[2,3]]. Its two zero equations force "
                    + "both coefficients to vanish. For target (r,s), the sum of the image is five times "
                    + "the sum of the input. Conversely r+s=5k gives the explicit integral preimage "
                    + "(r-2k,s-2k). No division by two or determinant-to-image inference is used."),
            Result("reset_square_image", "reset-square-image", "Exact ordinary image",
                Scope(Iff(Ex(Equal(L(I("v")), I("y")), B("v", M)),
                    Equal(Call("resetSquareReadout", I("q"), I("y")), Num(0))), false, B("y", M)),
                "Obstruction(r) is zero for r=0, (ZMod 2)^2 for r=1, ZMod 5 for r=2 and Int^2 for r=3. "
                    + "resetSquareReadout applies the independent normal codomain coordinates and reads the "
                    + "head: no readout, the two coefficients modulo two, their sum modulo five, or the "
                    + "two coefficient differences. At q=1 it reads both literal coefficients modulo two. "
                    + "The length-one plus-swap image theorem is reused for both resonant blocks. "
                    + "All inverse images are reconstructed by the integral domain equivalence."),
            Result("reset_square_readout_surjective", "reset-square-readout-onto", "Primitive arithmetic readout",
                Scope(Call("Surjective", Call("resetSquareReadout", I("q"))), false),
                "Each block readout is onto; inverse codomain coordinates return its chosen head and zero "
                    + "tail to the actual row lattice. Mathlib quotKerEquivOfSurjective and the exact image "
                    + "criterion construct resetSquareCokernelEquiv. Thus the ordinary quotient by the image "
                    + "alone is zero, (ZMod 2)^2, ZMod 5 or Int^2 in residues zero, one, two or three."),
            Result("reset_square_kernel", "reset-square-kernel", "Full primitive kernel",
                Scope(Iff(Equal(L(I("v")), Num(0)), Call("if",
                    Equal(Call("mod", I("q"), Num(4)), Num(3)),
                    Call("ExistsUnique", I("IntPair"), Call("kernelParameterEquation", I("q"), I("v"))),
                    Equal(I("v"), Num(0)))), false, B("v", M)),
                "kernelParameterEquation(q,v)(k) means v=resetSquareKernelVector(q,k). "
                    + "The generator antiRow is resetOddVector(1)(0), with coefficients (1,-1). "
                    + "At residue three the two head seeds are k(first) antiRow and k(second) antiRow; "
                    + "normalDomainEquiv inverse with zero tail constructs the full vector. The parameters "
                    + "are unique. In the other residues the kernel is zero. Length one is doubling on Int^2."),
            Result("reset_five_clock_time", "reset-five-clock-time", "Genuine time advances the five-clock",
                Scope(Equal(Clock(Call("transition", Call("resetMatrix", I("q")), I("v"))),
                    Call("mul", Num(3), Clock(I("v")))), true, B("v", M)),
                "Let aug(x)=coeff(x,1)+coeff(x,tau). clockWeight(i) repeats 1,2,0,4 in ZMod 5. "
                    + "resetFiveClock(v)=sum clockWeight(i) aug(v(i)). The recurrence w(i+1)=3w(i)-1 "
                    + "and terminal w(q-1)=2 telescope the true reset head and successors. "
                    + "Right multiplication by tau preserves augmentation, and 3 times 2 is 1 modulo five. "
                    + "This proves the scalar three for the original time, not for complement."),
            Result("reset_five_clock_surjective", "reset-five-clock-onto", "Primitive five-character",
                Scope(Call("Surjective", Call("resetFiveClock", I("q"))), false),
                "An integer coefficient at vertex zero and sign one reaches any ZMod 5 residue, since "
                    + "w(0)=1. This primitivity holds at every positive length; the image and time laws "
                    + "require q=2 modulo four."),
            Result("reset_five_clock_image", "reset-five-clock-exact-image", "The clock detects exactly the ordinary image",
                Scope(Equal(Call("range", Call("resetSquareDefect", I("q"))),
                    Call("ker", Call("resetFiveClock", I("q")))), true),
                "Time equivariance gives clock((id+T squared)v)=(1+3 squared)clock(v)=0. "
                    + "The reverse inclusion uses the independently established ordinary cokernel ZMod 5: "
                    + "the descended clock is onto, hence its conjugate is an onto endomorphism of the finite "
                    + "five-element set and is injective. Quotient zero is therefore equivalent to clock zero."),
            new DocumentBlock.Section(H("The primitive resonant pair at q=4m+3"), Blocks(
            Paragraph(Text("Take m>=0, q=4m+3 and n=4m+1, so q=n+2>0; m=0 is the full length-three "
                + "case. Put J=resetFlip and C=FiniteCompanionSquareDefect.codomainEquiv(J,n). "
                + "Put L=resetSquareDefect(q), the original id+T squared on every Fin q row and both integer "
                + "coefficients. If z=C(y), write its residual head pair as (r,s) and its complete "
                + "tail as t. In residue three headCodomainEquiv is identity, so normalCodomainEquiv "
                + "and C have the same value on y. With delta(x)=coeff(x,1)-coeff(x,tau), "
                + "resetSquareReadout(q)(y)=(delta(r),delta(s)), in Obstruction(3)=Int^2. "
                + "This is an ordered pair of primitive coefficient differences, not a change to "
                + "sum-and-difference eigenvector coordinates.")),
            Paragraph(Text("For domain seeds (a,b), the two raw image heads are "
                + "((id+J)(a+b),(id+J)b), and the tail is identity. The column shear "
                + "(a,b)->(a+b,b) has inverse (u,w)->(u-w,w). The existing length-one "
                + "plus-swap image criterion says x lies in the image of id+J exactly when "
                + "delta(x)=0. Hence L(v)=y is solvable exactly when delta(r)=delta(s)=0. "
                + "When both differences vanish, choose u,w with u+Ju=r and w+Jw=s; reconstruct(n,u-w,w,t) is an integral "
                + "preimage of y. All suffix coordinates remain in t. Conversely the two "
                + "differences vanish on the actual defect image, by this same two-head reduction.")),
            Paragraph(Text("For any integers k,l, choose residual heads single(1,k),single(1,l) "
                + "and zero tail, and apply C inverse. The readout is exactly (k,l), so it reaches "
                + "both primitive integer coefficients independently. Specializing reset_square_image, "
                + "reset_square_readout_surjective and resetSquareCokernelEquiv therefore gives "
                + "VertexModule(Sign,q)/image(id+T squared) equivalent as an Int-module to Int^2. "
                + "The quotient uses the image alone; no kernel is added and no hidden order-two "
                + "torsion remains. This is a quotient isomorphism, without any assertion that "
                + "separately chosen named equivalence values are equal.")))),
            new DocumentBlock.Section(H("Native resonant image and ordinary quotient"), Blocks(
            Paragraph(Text("For q>0, let E=resetNativeEquiv(q,hq) from the original stationary "
                + "dimension group Gq to VertexModule(Sign,q). The existing resetNativeEquiv_theta "
                + "law is E(resetTheta(q)(x))=T(E(x)); applying it twice gives "
                + "E(resetTheta(q)(resetTheta(q)(x)))=T(T(E(x))). Additivity therefore transports "
                + "id+resetTheta squared to id+T squared. Its exact native image test is "
                + "x in image(id+resetTheta squared) iff resetSquareReadout(q)(E(x))=0. "
                + "At q=4m+3 this is exactly the two primitive differences of the residual heads "
                + "of C(E(x)), including m=0. Since E and the readout are onto, the ordinary "
                + "native quotient Gq/image(id+resetTheta squared) is equivalent as an Int-module to Int^2 in this residue. "
                + "These identifications require hq and the actual time intertwining; they make "
                + "no coordinatewise positive-cone claim. Gaussian here only names the quarter-turn "
                + "period-four recurrence; it supplies no additional Gaussian-ring isomorphism, "
                + "combined image-plus-kernel quotient, or arbitrary-time classification.")))),
            Paragraph(Text("resetNativeEquiv(q,hq) identifies the original stationary dimension group Gq with "
                + "this lattice and intertwines resetTheta with the actual transition. Consequently the ordinary "
                + "native kernel and cokernel have exactly these four cases. In residue two the native five-clock "
                + "is the weighted augmentation after this equivalence. Existing rho_unitShift identifies the representation of "
                + "the actual history unit shift with resetTheta; rho.map_mul identifies its square. "
                + "Nonzero clock residues follow 1 -> 3 -> 4 -> 2 -> 1. An actual rho(h)=id+resetTheta squared "
                + "must be an integral equivalence, so four divides q. This is a necessary condition; no history "
                + "realization converse, full centralizer, Gaussian combined quotient or arbitrary-time "
                + "classification is asserted. These are repository-derived consequences with no literature "
                + "novelty claim.")))));
}
