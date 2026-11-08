using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinFactor;

internal sealed class OriginalUnitSupportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite original-table support obstruction on an arbitrary real normed carrier.",
        H("A support-state prerequisite for original affine identification"),
        Blocks(
            Paragraph(Text("E is any real normed vector space, including incomplete spaces. S is a symmetric real bilinear map E x E -> E, u is its unit, and norm(S(x,x)) = norm(x)^2 for every original x. D is the same total function E x E -> E throughout. P is a set of real linear readings separating original elements. P2(S,D,P) means that every reading in P makes the actual directed two-table positive semidefinite: each entry at labels v,w is alpha(S(v,w))-i alpha(D(v,w)), including both unknown diagonal responses. Hermitian positivity itself annihilates the diagonal D readings. Readings are not normalized in P2; zero, unequal and subnormalized masses remain permitted.")),
            Paragraph(Text("PB(S,D,P) is the complete original balance for every reading alpha in P and every a,b,c in E. With nu = D(a,b)-S(a,c), omega = S(a,b)+D(a,c), and Qalpha(v,w)=alpha(S(v,v))+alpha(S(w,w))+2 alpha(D(v,w)), it states Qalpha(b+nu,c+omega)=Qalpha(b-nu,c-omega). Expanding only the known S and using separation derives the element equality D(b+nu,c+omega)-D(b-nu,c-omega) = -2 S(b,nu)-2 S(c,omega). No input sum or scalar is expanded through D. OriginalSupportStage(E,S,D,P,u) in the displayed formula means exactly P2, PB, symmetry and bilinearity of S, S(u,x)=x, the square norm identity, and the stated separation by P.")),
            Describe.Lean(
                DescribeId.Create("original-unit-support-obstruction"),
                DeclarationHandle.Create("D5/S3/Quantum/SpinFactor/OriginalUnitSupport.support_unit_obstruction"),
                H("Support readings annihilate the second original label"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every real mu and original b, write h = D(mu u,b). Choose alpha in P with alpha(u)=1 and abs(alpha(x)) <= norm(x) for every original x. NormalizedContractive(alpha,u) denotes precisely these two requirements. For every nonzero real Z with alpha(h)=Z and abs(Z)=norm(h), both alpha(S(b,h)) and alpha(b) vanish. No state attaining a norm is constructed or assumed to be an actual physical preparation. The theorem quantifies over each supplied mathematical support reading.")),
                    Paragraph(Text("Positivity of the actual two-table gives the determinant bound with its real Jordan term retained. Separation then makes all scalar-unit input pairs have zero D. Let B(x,y)=alpha(S(x,y)) and w=h-Zu. Contractivity and the square norm identity give B(w,w)=0. Nonnegativity of B(x+t w,x+t w), through the real quadratic discriminant, gives B(w,x)=0 for every x; this is a statement about the known Jordan form and does not descend D to a quotient.")),
                    Paragraph(Text("Set k=mu Z/(1+mu^2), nu=h-mu k u and omega=mu b. The actual PB labels a=mu u, b=b, c=ku have inner values h and zero. Their outer pairs are rplus=b+nu, splus=ku+omega and rminus=b-nu, sminus=ku-omega. Exactly splus=mu rplus-mu w and sminus=-mu rminus-mu w. Since w is null for B, both actual outer Gram determinants are zero, so P2 reads both unknown outer D values as zero. PB then gives alpha(S(b,h))=0. The support identity makes this Z alpha(b), and Z nonzero gives alpha(b)=0. All labels are finite original linear combinations; no regularity or output closure of D enters.")),
                    Paragraph(Text("This is the support-zero-face inference of small-window Unit Bridge 99.2, an upstream component of the general unit-row route used by central 16.2 and 36.1. Its interpretation on a JB original candidate still requires the recovered same S and norm, the exact cone extension of P2 to mathematical readings, and a norm-support state with the listed properties. It does not establish those recovery and state-existence bridges.")),
                    Paragraph(Text("The full central target remains: for every original x,y in the actual U=span(h,k,j), j=D(h,k), and all real T,s,t, D(x,Tu+y)=x cross y and D(su+x,tu+y)=x cross y. Pure response identification and the generated frame of central 63.1, transverse unit transport of 36.1, and general original SO(2) invariance must be proved on this same E before that target can use them. This theorem supplies none of them as a premise or conclusion. E is not replaced by a four-dimensional carrier; its own JB completion need not fill the ambient selfadjoint part. All zero and dependent target branches and the full original quantum-source and consumer conditions remain part of that larger obligation. Mathematical readings do not supply actual preparations, instruments, joint systems, legal histories, physical clocks, energy or action constants."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-positive-support-unit-boundary"),
                DeclarationHandle.Create("D5/S3/Quantum/SpinFactor/OriginalUnitSupport.positive_support_unit_boundary"),
                H("Nonzero unit support excludes the closed semidefinite boundary"),
                StatementSource.FromAuthor(F.Disp(BoundaryStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Keep the entire original support stage, and let C be any set accurately determined by P: x belongs to C if and only if alpha(x) is nonnegative for every alpha in P. The supplied beta is any real linear mathematical reading nonnegative on C, with beta(u)=1 and abs(beta(x))<=norm(x). It need not belong to P. For h=D(mu u,b), retain every nonzero support requirement beta(h)=Z, abs(Z)=norm(h), Z nonzero. The conclusion is mu nonzero and abs(t)<norm(b-tu) for every real t. In particular no such nonzero support realization exists when mu=0, b=0, or norm(b-tu)<=abs(t) for even one real t; equality is included in the excluded boundary.")),
                    Paragraph(Text("For each complex two-column z, form the original element Wz from the squared moduli of its coefficients multiplying S(a,a), S(b,b), twice their real overlap multiplying S(a,b), and twice their imaginary overlap multiplying D(a,b). Original Hermitian P2 and separation give the same D's skew symmetry. Every original reading of Wz is its nonnegative actual table quadratic value, so exactness puts Wz in C. Positivity of beta then proves the full directed P2 table for beta, including arbitrary original labels and unknown diagonal responses. The original finite-difference equality also gives PB for every real linear reading. These statements neither descend D nor require any output subspace closure.")),
                    Paragraph(Text("Apply the existing support obstruction to the whole positive dual of C; original P is a subset, so separation is retained. This gives beta(b)=0. If norm(b-tu)<=abs(t), contractivity and the square norm identity bound beta((b-tu)^2) by t^2. Expanding the known Jordan product and using beta(b)=0 gives beta(b^2)<=0. P2 for the original pair (mu u,b) then gives Z^2<=mu^2 beta(b^2)<=0, contradicting Z nonzero. This is a test of the nonzero support telescope, not a zero-output witness substituted into it.")),
                    Paragraph(Text("In a recovered original JB stage, positive or negative elements have the displayed closed norm-ball property. That implication, existence of a positive norm-support reading on the full original carrier, and the recovery of this stage from the full original A1-A3 are not established by this declaration. The general nonzero support telescope outside these balls remains unresolved here: no complete nonzero model and no general impossibility proof is supplied. This proves a necessary obstruction and the exact-cone reading bridge, not all unit rows or the transverse row of central 36.1. The complete original central 76.2 and 77.1 remain open with the same E, cone, D, generated U, all zero and dependent branches, and all source and quantum-consumer conditions. The unfinished four-slot audit is tracked in issue 28178."))),
                DescribeRole.Theorem))));

    private static Formula BoundaryStatement()
    {
        var e = V("E"); var s = V("S"); var d = V("D"); var p = V("P"); var u = V("u");
        var target = And(new Formula.Relation(V("mu"), FormulaRelationOperator.NotEqual, Num(0)),
            All("t", V("R"), new Formula.Relation(Call("abs", V("t")),
                FormulaRelationOperator.LessThan, Call("norm", Subtract(V("b"), Multiply(V("t"), u))))));
        return All("E", V("RealNormedSpaces"), All("S", Call("RealBilinearMaps", e),
            All("D", Call("TotalBinaryMaps", e), All("P", Call("ReadingFamilies", e), All("u", e,
            All("C", Call("Subsets", e), Imp(And(Call("OriginalSupportStage", e, s, d, p, u),
                Call("ConeExact", V("C"), p)),
            All("mu", V("R"), All("b", e, All("beta", Call("RealLinearReadings", e),
            All("Z", V("R"), Imp(Call("PositiveNormalizedContractiveNonzeroSupport",
                V("beta"), V("C"), u, Call("D", Multiply(V("mu"), u), V("b")), V("Z")), target))))))))))));
    }

    private static Formula V(string s) => Id(s);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Read(Formula x) => Call("alpha", x);
    private static Formula Statement()
    {
        var e = V("E"); var s = V("S"); var d = V("D"); var p = V("P"); var u = V("u");
        var h = Call("D", Multiply(V("mu"), u), V("b"));
        var premise = And(new Formula.Relation(V("Z"), FormulaRelationOperator.NotEqual, Num(0)),
            And(Equal(Read(h), V("Z")), Equal(Call("abs", V("Z")), Call("norm", h))));
        var conclusion = And(Equal(Read(Call("S", V("b"), h)), Num(0)), Equal(Read(V("b")), Num(0)));
        return All("E", V("RealNormedSpaces"),
            All("S", Call("RealBilinearMaps", e), All("D", Call("TotalBinaryMaps", e),
            All("P", Call("ReadingFamilies", e), All("u", e,
            Imp(Call("OriginalSupportStage", e, s, d, p, u),
            All("mu", V("R"), All("b", e, All("alpha", p,
            Imp(Call("NormalizedContractive", V("alpha"), u), All("Z", V("R"),
                Imp(premise, conclusion))))))))))));
    }
}
