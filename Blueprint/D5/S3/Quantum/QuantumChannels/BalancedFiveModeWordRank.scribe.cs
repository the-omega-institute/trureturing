using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class BalancedFiveModeWordRankDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform homogeneous rank for the balanced five-mode reflection family under injective algebra transport.",
        H("Balanced five-mode terminal word rank"),
        Blocks(Describe.Lean(DescribeId.Create("balanced-five-mode-lifted-word-rank"),
            DeclarationHandle.Create("D5/S3/Quantum/QuantumChannels/BalancedFiveModeWordRank.framed_balanced_word_rank"),
            H("Exact rank with a faithful lift and nonzero weights"),
            StatementSource.FromAuthor(TheoremFormula()), AssessedProvenance.FromRepo(), Blocks(
                Paragraph(Text("U=reflection0(a,b) and V=reflection1(c) are the explicit five-by-five matrices "
                    + "in the Lean source. U has the block [[a,b],[b,-a]] on configurations 0 and 4 and fixes "
                    + "configurations 1,2,3. V is the symmetric signed square, with coefficient c, negative "
                    + "edge 0–3, and fixed configuration 4. The parameters are complex; no positivity or "
                    + "self-adjointness is required by this algebraic theorem. E is any finite-dimensional "
                    + "complex algebra and f is an injective unital complex algebra homomorphism.")),
                Paragraph(Text("For R=UV the proof establishes R^4+(a+1)R^3-(a+1)R-I=0 and independence "
                    + "of I,R,R^2,R^3. Entries (0,0),(0,4),(4,0),(1,2) form a minor of determinant "
                    + "c b^2(1-a), nonzero under the stated assumptions. The quartic supplies both forward "
                    + "and inverse power-space closure. These facts provide the lower and upper bounds at "
                    + "every length through TwoInvolutionWordRank.homogeneous_word_rank.")),
                Paragraph(Text("For the fixed V2 source in RECURSIVE_RELATIONAL_OBSERVATION_MINIMAL_RECORD_DILATIONS, "
                    + "equations (1.2),(1.3),(2.6),(2.8), restrict p=q>0, r>0, 2p+r<1. Put "
                    + "A=1-2p-r, B=1-2p, t=2p, a=sqrt(A)/sqrt(B), b=sqrt(r)/sqrt(B), c=1/sqrt(2), "
                    + "z=sqrt(B), w=sqrt(t). The published frames G=(I,-iX,iY,-iZ,-iY) give "
                    + "f(X)=D†(X⊗I₂)D on all C⁵⊗C², where D is the block diagonal matrix of G_i†. "
                    + "The exact published operators are z f(U) and w f(V). All strict parameters obey "
                    + "the displayed hypotheses, without a probability cutoff.")),
                Paragraph(Text("Composition with independently supplied fresh environments gives the exact "
                    + "length-N Kraus products. Watrous, The Theory of Quantum Information, Chapter 2, "
                    + "Theorem 2.22 and Corollary 2.27, and Sanz, Pérez-García, Wolf and Cirac, "
                    + "A quantum version of Wielandt’s inequality, arXiv:0909.5347, Section II, supply the standard Choi vectorization and minimum "
                    + "pure-environment interpretation: the terminal rank is min(N+1,4). This yields an "
                    + "abstract terminal pure environment and equality on every untouched reference extension. "
                    + "The original one-step minimum, measured flag recovery and two-step unread comparison "
                    + "remain their existing owners.")),
                Paragraph(Text("Repeated action of the published balanced controlled interaction on the same "
                    + "retained environment has period two and is distinct from these channel powers. "
                    + "The terminal dimension does not supply measured Markov histories, independent arbitrary "
                    + "coherent path archives, native alpha/beta acquisition, physical controls, finite precision "
                    + "or actual record outputs. An unlimited archive bound requires a separate input and "
                    + "readout contract."))), DescribeRole.Theorem))));

    private static Formula C => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Call(string n, params Formula[] x) => new Formula.FunctionCall(FormulaIdentifier.Create(n), [.. x]);
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n),t);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x,FormulaRelationOperator.Equal,y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x,FormulaBinaryOperator.Add,y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x,FormulaBinaryOperator.Multiply,y);
    private static Formula Sq(Formula x) => Seq(x, Caret, Grp(Num(2)));
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x,FormulaLogicOperator.And,y);
    private static Formula TheoremFormula()
    {
        Formula e=F.Id("E"), f=F.Id("f"), a=F.Id("a"), b=F.Id("b"), c=F.Id("c"),
            z=F.Id("z"), w=F.Id("w"), n=F.Id("n");
        Formula nz(Formula x) => new Formula.Relation(x,FormulaRelationOperator.NotEqual,Num(0));
        Formula h=And(Call("Injective",f),And(Eq(Add(Sq(a),Sq(b)),Num(1)),
            And(Eq(Mul(Num(2),Sq(c)),Num(1)),And(nz(b),And(nz(c),
            And(new Formula.Relation(a,FormulaRelationOperator.NotEqual,Num(1)),And(nz(z),nz(w))))))));
        Formula u=Call("smul",z,Call("apply",f,Call("reflection0",a,b)));
        Formula v=Call("smul",w,Call("apply",f,Call("reflection1",c)));
        return Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [B("E",Call("FiniteDimensionalComplexAlgebra")),
             B("f",Call("AlgHom",C,Call("Matrix",Num(5),Num(5),C),e)),
             B("a",C),B("b",C),B("c",C),B("z",C),B("w",C),B("n",N)],
            new Formula.Logic(h,FormulaLogicOperator.Implies,
                Eq(Call("finrank",C,Call("wordSpace",u,v,n)),Call("min",Add(n,Num(1)),Num(4))))));
    }
}
