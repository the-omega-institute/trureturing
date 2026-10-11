# The Finite Cosine Cutoff Kernel

## Abstract

The actual finite cosine cutoff has ordinary and L2 inverse identities, an all-L2 convolution operator, and an actual weighted integral client.

**Theorem 1.1 (Every positive lower cutoff and every larger finite upper cutoff).**

$$\forall c \in \mathbb{R}, N \in \mathbb{R},\; 0 < c \Rightarrow \left(c \le N \Rightarrow \left(\operatorname{Measurable}\left(\operatorname{symbol}\left(c, N\right)\right) \land \left(\operatorname{Integrable}\left(\operatorname{symbol}\left(c, N\right), volume\right) \land \left(\operatorname{MemLp}\left(\operatorname{symbol}\left(c, N\right), 2, volume\right) \land \left(\left(\forall xi \in \mathbb{R},\; \operatorname{norm}\left(\operatorname{symbol}\left(c, N, xi\right)\right) \le \frac{2 \cdot \pi}{c}\right) \land \left(\left(\forall M \in \mathbb{R},\; N \le M \Rightarrow \left(\forall xi \in \mathbb{R},\; \operatorname{norm}\left(\operatorname{symbol}\left(c, M, xi\right) - \operatorname{symbol}\left(c, N, xi\right)\right) \le \frac{2 \cdot \pi}{N}\right)\right) \land \left(\left(\forall x \in \mathbb{R},\; \operatorname{FourierInv}\left(\operatorname{symbol}\left(c, N\right), x\right) = \operatorname{ofReal}\left(\operatorname{kernel}\left(c, N, x\right)\right)\right) \land \left(\operatorname{kernel}\left(c, N, 0\right) = -{2} \cdot \operatorname{log}\left(\frac{N}{c}\right) \land \left(c = N \Rightarrow \left(\left(\forall x \in \mathbb{R},\; \operatorname{kernel}\left(c, N, x\right) = 0\right) \land \left(\left(\forall rho \in {\mathbb{R}\to \mathbb{R}},\; \forall f \in {\mathbb{R}\to \mathbb{R}},\; \forall x \in \mathbb{R},\; \int_{\mathbb{R}} \operatorname{kernel}\left(c, N, x - y\right) \cdot \operatorname{f}\left(y\right) \cdot \operatorname{rho}\left(y\right) dy = 0\right) \land \left(\operatorname{AEEq}\left(\operatorname{symbol}\left(c, N\right), (xi: \mathbb{R} \mapsto 0), volume\right) \land \left(\operatorname{symbol}\left(c, N, \frac{c}{2 \cdot \pi}\right) \ne 0 \land \operatorname{symbol}\left(c, N, -{\frac{c}{2 \cdot \pi}}\right) \ne 0\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CosineCutoffKernel.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The real physical kernel is the actual oriented interval integral below. The symbol is complex valued and has closed frequency endpoints. All integrals use Lebesgue measure.$\operatorname{kernel}\left(c, N, x\right) = -{2} \cdot \int_{c}^{N} \frac{\operatorname{cos}\left(t \cdot x\right)}{t} dt$`D5/S3/Fourier/Asymptotics/CosineCutoffKernel.kernel`

$\operatorname{symbol}\left(c, N, xi\right) = \operatorname{ite}\left(\frac{c}{2 \cdot \pi} \le \left|xi\right| \land \left|xi\right| \le \frac{N}{2 \cdot \pi}, \operatorname{ofReal}\left(-{\frac{1}{\left|xi\right|}}\right), 0\right)$`D5/S3/Fourier/Asymptotics/CosineCutoffKernel.symbol`

FourierInv denotes the ordinary inverse integral with the positive phase, dual to the forward exp(-2*pi*i*x*xi) convention. Its exact integral is displayed here.$\operatorname{FourierInv}\left(\operatorname{symbol}\left(c, N\right), x\right) = \int_{\mathbb{R}} \operatorname{exp}\left(\operatorname{ofReal}\left(2 \cdot \pi \cdot xi \cdot x\right) \cdot i\right) \cdot \operatorname{symbol}\left(c, N, xi\right) dxi$

The positive and reflected negative bands are disjoint because c is positive. Pairing their exponential phases gives twice the real cosine. The substitution t=2*pi*xi gives the physical interval integral with its minus-two coefficient.

The symbol is measurable, Lebesgue integrable, and in complex L2. Its pointwise norm is at most 2*pi/c. For every real M at least N, the pointwise difference of the symbols with upper cutoffs M and N is at most 2*pi/N.

At x=0 the physical kernel is -2*log(N/c). At N=c the physical kernel and every ordinary real weighted integral action are zero. The closed symbol is zero almost everywhere, and is nonzero at both frequencies c/(2*pi) and -c/(2*pi). The weighted zero action quantifies over every pair of real functions rho and f.

This statement establishes ordinary finite inverse integration and finite symbol estimates. The public finite-window theorem also identifies the actual L2 inverse representative of this same symbol with the complex-valued kernel in L2, including its almost-everywhere representative equality.`D5/S3/Fourier/Asymptotics/CosineCutoffKernel.actual_cutoff_inverse`

The positive-Ci cutoff limit and the original Gaussian series and path conclusions remain separate obligations.

**Theorem 1.2 (The actual L2 inverse and its kernel representative).**

$$\forall c \in \mathbb{R},\; \forall N \in \mathbb{R},\; 0 < c \Rightarrow \left(c \le N \Rightarrow \left(\exists hm \in \operatorname{MemLp}\left(\operatorname{symbol}\left(c, N\right), 2, volume\right), hq \in \operatorname{MemLp}\left((x: \mathbb{R} \mapsto \operatorname{ofReal}\left(\operatorname{kernel}\left(c, N, x\right)\right)), 2, volume\right),\; \operatorname{AEEq}\left(\operatorname{coeFn}\left(\operatorname{L2FourierInverse}\left(\operatorname{toLp}\left(hm, \operatorname{symbol}\left(c, N\right)\right)\right)\right), (x: \mathbb{R} \mapsto \operatorname{ofReal}\left(\operatorname{kernel}\left(c, N, x\right)\right)), volume\right) \land \operatorname{L2FourierInverse}\left(\operatorname{toLp}\left(hm, \operatorname{symbol}\left(c, N\right)\right)\right) = \operatorname{toLp}\left(hq, (x: \mathbb{R} \mapsto \operatorname{ofReal}\left(\operatorname{kernel}\left(c, N, x\right)\right))\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CosineCutoffKernel.actual_cutoff_inverse` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For c>0 and c<=N, let m be the existing closed-band symbol and q(x)=ofReal(kernel(c,N,x)). The statement supplies proofs hm and hq that these two specific functions belong to complex L2(volume).

L2FourierInverse denotes the inverse of Lp.fourierTransformₗᵢ ℝ ℂ. toLp(h,f) is the L2 class constructed from the displayed MemLp witness; coeFn is its measurable representative. The first equality is almost everywhere for volume. The second is equality of L2 elements.

This theorem identifies the inverse transform of m itself. It makes no assertion about the convolution of q with arbitrary L2 inputs, weighted operators, or the positive-Ci limit.

**Theorem 1.3 (The ordinary convolution on every complex L2 input).**

$$\forall c \in \mathbb{R},\; \forall N \in \mathbb{R},\; 0 < c \Rightarrow \left(c \le N \Rightarrow \left(\operatorname{MemLp}\left((x: \mathbb{R} \mapsto \operatorname{ofReal}\left(\operatorname{kernel}\left(c, N, x\right)\right)), 2, volume\right) \land \left(\exists C \in \operatorname{ContinuousLinearMap}\left(\mathbb{C}, \operatorname{Lp}\left(\mathbb{C}, 2, volume\right), \operatorname{Lp}\left(\mathbb{C}, 2, volume\right)\right),\; \left(\forall f \in \operatorname{Lp}\left(\mathbb{C}, 2, volume\right),\; \forall x \in \mathbb{R},\; \operatorname{Integrable}\left((y: \mathbb{R} \mapsto \operatorname{ofReal}\left(\operatorname{kernel}\left(c, N, x - y\right)\right) \cdot \operatorname{f}\left(y\right)), volume\right)\right) \land \left(\left(\forall f \in \operatorname{Lp}\left(\mathbb{C}, 2, volume\right),\; \exists hg \in \operatorname{MemLp}\left((xi: \mathbb{R} \mapsto \operatorname{symbol}\left(c, N, xi\right) \cdot \operatorname{eval}\left(\operatorname{L2Fourier}\left(f\right), xi\right)), 2, volume\right),\; \exists hconv \in \operatorname{MemLp}\left((x: \mathbb{R} \mapsto \operatorname{integral}\left((y: \mathbb{R} \mapsto \operatorname{ofReal}\left(\operatorname{kernel}\left(c, N, x - y\right)\right) \cdot \operatorname{f}\left(y\right)), volume\right)), 2, volume\right),\; \operatorname{AEEq}\left(\operatorname{coeFn}\left(\operatorname{C}\left(f\right)\right), (x: \mathbb{R} \mapsto \operatorname{integral}\left((y: \mathbb{R} \mapsto \operatorname{ofReal}\left(\operatorname{kernel}\left(c, N, x - y\right)\right) \cdot \operatorname{f}\left(y\right)), volume\right)), volume\right) \land \left(\operatorname{C}\left(f\right) = \operatorname{toLp}\left(hconv, (x: \mathbb{R} \mapsto \operatorname{integral}\left((y: \mathbb{R} \mapsto \operatorname{ofReal}\left(\operatorname{kernel}\left(c, N, x - y\right)\right) \cdot \operatorname{f}\left(y\right)), volume\right))\right) \land \operatorname{C}\left(f\right) = \operatorname{L2FourierInverse}\left(\operatorname{toLp}\left(hg, (xi: \mathbb{R} \mapsto \operatorname{symbol}\left(c, N, xi\right) \cdot \operatorname{eval}\left(\operatorname{L2Fourier}\left(f\right), xi\right))\right)\right)\right)\right) \land \left(\operatorname{norm}\left(C\right) \le \frac{2 \cdot \pi}{c} \land \left(\forall M \in \mathbb{R},\; N \le M \Rightarrow \left(\exists D \in \operatorname{ContinuousLinearMap}\left(\mathbb{C}, \operatorname{Lp}\left(\mathbb{C}, 2, volume\right), \operatorname{Lp}\left(\mathbb{C}, 2, volume\right)\right),\; \left(\forall f \in \operatorname{Lp}\left(\mathbb{C}, 2, volume\right),\; \operatorname{AEEq}\left(\operatorname{coeFn}\left(\operatorname{D}\left(f\right)\right), (x: \mathbb{R} \mapsto \operatorname{integral}\left((y: \mathbb{R} \mapsto \operatorname{ofReal}\left(\operatorname{kernel}\left(c, M, x - y\right)\right) \cdot \operatorname{f}\left(y\right)), volume\right)), volume\right)\right) \land \operatorname{norm}\left(D - C\right) \le \frac{2 \cdot \pi}{N}\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CosineCutoffKernel.actual_cutoff_convolution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

HC is Lp(C,2,volume), and CLMC(HC,HC) is its space of complex continuous linear maps. L2Fourier and L2FourierInverse are the mutually inverse Lp Fourier isometries with the exp(-2*pi*i*x*xi) forward convention.

Every input f belongs to the full complex L2 space. For every real x, the actual integral row q(x-y)f(y) is integrable. The displayed MemLp witnesses supply the spatial integral and the frequency product as L2 elements. Both are identified with the same operator output, with the inverse transform applied to the frequency product.

The nested estimate quantifies over every real M>=N. Its operator D is identified almost everywhere with the ordinary convolution using kernel(c,M). Only the frequency functions m, phase*m and m*L2Fourier(f) use bounded support.

**Theorem 1.4 (The actual weighted integral operator and its density conjugacy).**

$$\forall r \in \mathbb{R},\; \forall alpha \in \mathbb{R},\; 0 < r \Rightarrow \left(r < 1 \Rightarrow \left(\forall c \in \mathbb{R},\; \forall N \in \mathbb{R},\; 0 < c \Rightarrow \left(c \le N \Rightarrow \left(\exists C \in \operatorname{ContinuousLinearMap}\left(\mathbb{R}, \operatorname{Lp}\left(\mathbb{R}, 2, volume\right), \operatorname{Lp}\left(\mathbb{R}, 2, volume\right)\right),\; \exists T \in \operatorname{ContinuousLinearMap}\left(\mathbb{R}, \operatorname{Lp}\left(\mathbb{R}, 2, \operatorname{withDensity}\left(volume, (x: \mathbb{R} \mapsto \operatorname{ennrealOfReal}\left(\frac{1}{4 \cdot \pi \cdot \operatorname{sqrt}\left(\frac{1 + r}{2} \cdot \frac{1 - r}{2}\right)} \cdot \operatorname{exp}\left(-{\frac{\left(\frac{1}{\frac{1 + r}{2}} + \frac{alpha \cdot alpha}{\frac{1 - r}{2}}\right) \cdot x \cdot x}{2}}\right)\right))\right)\right), \operatorname{Lp}\left(\mathbb{R}, 2, \operatorname{withDensity}\left(volume, (x: \mathbb{R} \mapsto \operatorname{ennrealOfReal}\left(\frac{1}{4 \cdot \pi \cdot \operatorname{sqrt}\left(\frac{1 + r}{2} \cdot \frac{1 - r}{2}\right)} \cdot \operatorname{exp}\left(-{\frac{\left(\frac{1}{\frac{1 + r}{2}} + \frac{alpha \cdot alpha}{\frac{1 - r}{2}}\right) \cdot x \cdot x}{2}}\right)\right))\right)\right)\right),\; \exists U \in \operatorname{LinearIsometryEquiv}\left(\mathbb{R}, \operatorname{Lp}\left(\mathbb{R}, 2, \operatorname{withDensity}\left(volume, (x: \mathbb{R} \mapsto \operatorname{ennrealOfReal}\left(\frac{1}{4 \cdot \pi \cdot \operatorname{sqrt}\left(\frac{1 + r}{2} \cdot \frac{1 - r}{2}\right)} \cdot \operatorname{exp}\left(-{\frac{\left(\frac{1}{\frac{1 + r}{2}} + \frac{alpha \cdot alpha}{\frac{1 - r}{2}}\right) \cdot x \cdot x}{2}}\right)\right))\right)\right), \operatorname{Lp}\left(\mathbb{R}, 2, volume\right)\right),\; \exists M \in \operatorname{ContinuousLinearMap}\left(\mathbb{R}, \operatorname{Lp}\left(\mathbb{R}, 2, volume\right), \operatorname{Lp}\left(\mathbb{R}, 2, volume\right)\right),\; \left(\forall f \in \operatorname{Lp}\left(\mathbb{R}, 2, volume\right),\; \operatorname{AEEq}\left(\operatorname{coeFn}\left(\operatorname{C}\left(f\right)\right), (x: \mathbb{R} \mapsto \operatorname{integral}\left((y: \mathbb{R} \mapsto \operatorname{kernel}\left(c, N, x - y\right) \cdot \operatorname{f}\left(y\right)), volume\right)), volume\right)\right) \land \left(\left(\forall f \in \operatorname{Lp}\left(\mathbb{R}, 2, \operatorname{withDensity}\left(volume, (x: \mathbb{R} \mapsto \operatorname{ennrealOfReal}\left(\frac{1}{4 \cdot \pi \cdot \operatorname{sqrt}\left(\frac{1 + r}{2} \cdot \frac{1 - r}{2}\right)} \cdot \operatorname{exp}\left(-{\frac{\left(\frac{1}{\frac{1 + r}{2}} + \frac{alpha \cdot alpha}{\frac{1 - r}{2}}\right) \cdot x \cdot x}{2}}\right)\right))\right)\right),\; \operatorname{AEEq}\left(\operatorname{coeFn}\left(\operatorname{T}\left(f\right)\right), (x: \mathbb{R} \mapsto \operatorname{integral}\left((y: \mathbb{R} \mapsto \operatorname{kernel}\left(c, N, x - y\right) \cdot \operatorname{f}\left(y\right)), \operatorname{withDensity}\left(volume, (x: \mathbb{R} \mapsto \operatorname{ennrealOfReal}\left(\frac{1}{4 \cdot \pi \cdot \operatorname{sqrt}\left(\frac{1 + r}{2} \cdot \frac{1 - r}{2}\right)} \cdot \operatorname{exp}\left(-{\frac{\left(\frac{1}{\frac{1 + r}{2}} + \frac{alpha \cdot alpha}{\frac{1 - r}{2}}\right) \cdot x \cdot x}{2}}\right)\right))\right)\right)), \operatorname{withDensity}\left(volume, (x: \mathbb{R} \mapsto \operatorname{ennrealOfReal}\left(\frac{1}{4 \cdot \pi \cdot \operatorname{sqrt}\left(\frac{1 + r}{2} \cdot \frac{1 - r}{2}\right)} \cdot \operatorname{exp}\left(-{\frac{\left(\frac{1}{\frac{1 + r}{2}} + \frac{alpha \cdot alpha}{\frac{1 - r}{2}}\right) \cdot x \cdot x}{2}}\right)\right))\right)\right)\right) \land \left(\left(\forall f \in \operatorname{Lp}\left(\mathbb{R}, 2, \operatorname{withDensity}\left(volume, (x: \mathbb{R} \mapsto \operatorname{ennrealOfReal}\left(\frac{1}{4 \cdot \pi \cdot \operatorname{sqrt}\left(\frac{1 + r}{2} \cdot \frac{1 - r}{2}\right)} \cdot \operatorname{exp}\left(-{\frac{\left(\frac{1}{\frac{1 + r}{2}} + \frac{alpha \cdot alpha}{\frac{1 - r}{2}}\right) \cdot x \cdot x}{2}}\right)\right))\right)\right),\; \operatorname{AlmostEverywhere}\left(\operatorname{withDensity}\left(volume, (x: \mathbb{R} \mapsto \operatorname{ennrealOfReal}\left(\frac{1}{4 \cdot \pi \cdot \operatorname{sqrt}\left(\frac{1 + r}{2} \cdot \frac{1 - r}{2}\right)} \cdot \operatorname{exp}\left(-{\frac{\left(\frac{1}{\frac{1 + r}{2}} + \frac{alpha \cdot alpha}{\frac{1 - r}{2}}\right) \cdot x \cdot x}{2}}\right)\right))\right), (x: \mathbb{R} \mapsto \operatorname{Integrable}\left((y: \mathbb{R} \mapsto \operatorname{kernel}\left(c, N, x - y\right) \cdot \operatorname{f}\left(y\right)), \operatorname{withDensity}\left(volume, (x: \mathbb{R} \mapsto \operatorname{ennrealOfReal}\left(\frac{1}{4 \cdot \pi \cdot \operatorname{sqrt}\left(\frac{1 + r}{2} \cdot \frac{1 - r}{2}\right)} \cdot \operatorname{exp}\left(-{\frac{\left(\frac{1}{\frac{1 + r}{2}} + \frac{alpha \cdot alpha}{\frac{1 - r}{2}}\right) \cdot x \cdot x}{2}}\right)\right))\right)\right))\right)\right) \land \left(\left(\forall f \in \operatorname{Lp}\left(\mathbb{R}, 2, \operatorname{withDensity}\left(volume, (x: \mathbb{R} \mapsto \operatorname{ennrealOfReal}\left(\frac{1}{4 \cdot \pi \cdot \operatorname{sqrt}\left(\frac{1 + r}{2} \cdot \frac{1 - r}{2}\right)} \cdot \operatorname{exp}\left(-{\frac{\left(\frac{1}{\frac{1 + r}{2}} + \frac{alpha \cdot alpha}{\frac{1 - r}{2}}\right) \cdot x \cdot x}{2}}\right)\right))\right)\right),\; \operatorname{AEEq}\left(\operatorname{coeFn}\left(\operatorname{U}\left(f\right)\right), (x: \mathbb{R} \mapsto \operatorname{sqrt}\left(\frac{1}{4 \cdot \pi \cdot \operatorname{sqrt}\left(\frac{1 + r}{2} \cdot \frac{1 - r}{2}\right)} \cdot \operatorname{exp}\left(-{\frac{\left(\frac{1}{\frac{1 + r}{2}} + \frac{alpha \cdot alpha}{\frac{1 - r}{2}}\right) \cdot x \cdot x}{2}}\right)\right) \cdot \operatorname{f}\left(x\right)), volume\right)\right) \land \left(\left(\forall h \in \operatorname{Lp}\left(\mathbb{R}, 2, volume\right),\; \operatorname{AEEq}\left(\operatorname{coeFn}\left(\operatorname{apply}\left(\operatorname{symm}\left(U\right), h\right)\right), (x: \mathbb{R} \mapsto \frac{\operatorname{h}\left(x\right)}{\operatorname{sqrt}\left(\frac{1}{4 \cdot \pi \cdot \operatorname{sqrt}\left(\frac{1 + r}{2} \cdot \frac{1 - r}{2}\right)} \cdot \operatorname{exp}\left(-{\frac{\left(\frac{1}{\frac{1 + r}{2}} + \frac{alpha \cdot alpha}{\frac{1 - r}{2}}\right) \cdot x \cdot x}{2}}\right)\right)}), \operatorname{withDensity}\left(volume, (x: \mathbb{R} \mapsto \operatorname{ennrealOfReal}\left(\frac{1}{4 \cdot \pi \cdot \operatorname{sqrt}\left(\frac{1 + r}{2} \cdot \frac{1 - r}{2}\right)} \cdot \operatorname{exp}\left(-{\frac{\left(\frac{1}{\frac{1 + r}{2}} + \frac{alpha \cdot alpha}{\frac{1 - r}{2}}\right) \cdot x \cdot x}{2}}\right)\right))\right)\right)\right) \land \left(\left(\forall h \in \operatorname{Lp}\left(\mathbb{R}, 2, volume\right),\; \operatorname{AEEq}\left(\operatorname{coeFn}\left(\operatorname{M}\left(h\right)\right), (x: \mathbb{R} \mapsto \operatorname{sqrt}\left(\frac{1}{4 \cdot \pi \cdot \operatorname{sqrt}\left(\frac{1 + r}{2} \cdot \frac{1 - r}{2}\right)} \cdot \operatorname{exp}\left(-{\frac{\left(\frac{1}{\frac{1 + r}{2}} + \frac{alpha \cdot alpha}{\frac{1 - r}{2}}\right) \cdot x \cdot x}{2}}\right)\right) \cdot \operatorname{h}\left(x\right)), volume\right)\right) \land \left(\operatorname{compose}\left(\operatorname{asCLM}\left(U\right), \operatorname{compose}\left(T, \operatorname{asCLM}\left(\operatorname{symm}\left(U\right)\right)\right)\right) = \operatorname{compose}\left(M, \operatorname{compose}\left(C, M\right)\right) \land \left(\operatorname{norm}\left(C\right) \le \frac{2 \cdot \pi}{c} \land \left(\operatorname{norm}\left(M\right) \le \operatorname{sqrt}\left(\frac{1}{4 \cdot \pi \cdot \operatorname{sqrt}\left(\frac{1 + r}{2} \cdot \frac{1 - r}{2}\right)}\right) \land \operatorname{norm}\left(T\right) \le \frac{1}{4 \cdot \pi \cdot \operatorname{sqrt}\left(\frac{1 + r}{2} \cdot \frac{1 - r}{2}\right)} \cdot \frac{2 \cdot \pi}{c}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CosineCutoffKernel.actual_weighted_cutoff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The parameters are r and alpha with 0<r<1. Define a=(1+r)/2, b=(1-r)/2, c0=1/(4*pi*sqrt(a*b)), kappa=1/a+alpha^2/b, rho(x)=c0*exp(-kappa*x^2/2), and mu=volume.withDensity(ofReal(rho)). The formula expands these definitions, with ennrealOfReal denoting ENNReal.ofReal. HR=Lp(R,2,volume), Hmu=Lp(R,2,mu).

T is obtained from the actual L2 integral-kernel factory applied to K(x,y)=kernel(c,N,x-y). Its ordinary weighted integral representative and almost-everywhere row integrability are established before the conjugacy is used. No identity for T or C is required as a caller hypothesis.

U is an onto real linear isometry between the two displayed measures; its inverse is also specified almost everywhere. M is multiplication by sqrt(rho). compose(A,B) means A after B, and asCLM denotes the continuous linear map underlying a linear isometry equivalence.

This finite-cutoff statement does not pass to the positive-Ci limit or assert any Gaussian quadratic-series or path-limit conclusion.

**Theorem 1.5 (The real finite convolution supplier).**

$$\forall c \in \mathbb{R},\; \forall N \in \mathbb{R},\; 0 < c \Rightarrow \left(c \le N \Rightarrow \left(\operatorname{Measurable}\left(\operatorname{kernel}\left(c, N\right)\right) \land \left(\operatorname{MemLp}\left(\operatorname{kernel}\left(c, N\right), 2, volume\right) \land \left(\exists C \in \operatorname{ContinuousLinearMap}\left(\mathbb{R}, \operatorname{Lp}\left(\mathbb{R}, 2, volume\right), \operatorname{Lp}\left(\mathbb{R}, 2, volume\right)\right),\; \left(\forall f \in \operatorname{Lp}\left(\mathbb{R}, 2, volume\right),\; \operatorname{AEEq}\left(\operatorname{coeFn}\left(\operatorname{C}\left(f\right)\right), (x: \mathbb{R} \mapsto \operatorname{integral}\left((y: \mathbb{R} \mapsto \operatorname{kernel}\left(c, N, x - y\right) \cdot \operatorname{f}\left(y\right)), volume\right)), volume\right)\right) \land \operatorname{norm}\left(C\right) \le \frac{2 \cdot \pi}{c}\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CosineCutoffKernel.actual_cutoff_real` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive c and every N>=c the actual real cutoff kernel is measurable and in real L2. Its ordinary real convolution is represented by a continuous linear map of norm at most 2*pi/c. This original-owner supplier is consumed by the actual positive-Ci high-pass L2 limit and operator construction.`D5/S3/Fourier/Asymptotics/CosineCutoffKernel/Highpass.actual_highpass_convolution`

**Theorem 1.6 (The actual bilinear L2 pairing).**

$$\forall f \in \operatorname{Lp}\left(\mathbb{C}, 2, volume\right),\; \forall g \in \operatorname{Lp}\left(\mathbb{C}, 2, volume\right),\; \operatorname{pair}\left(f, g\right) = \operatorname{integral}\left((x: \mathbb{R} \mapsto \operatorname{f}\left(x\right) \cdot \operatorname{g}\left(x\right)), volume\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CosineCutoffKernel.pair_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every two complex L2 elements f and g, the original bilinear map pair evaluates to the integral of f(x)g(x), without complex conjugation. pair is the L2 pairing induced by complex multiplication. This supplier identifies the high-pass convolution integral under translation-reflection.`D5/S3/Fourier/Asymptotics/CosineCutoffKernel.pair``D5/S3/Fourier/Asymptotics/CosineCutoffKernel/Highpass.actual_highpass_convolution`

**Theorem 1.7 (Integrability of complex L2 products).**

$$\forall a \in {\mathbb{R}\to \mathbb{C}},\; \forall b \in {\mathbb{R}\to \mathbb{C}},\; \operatorname{MemLp}\left(a, 2, volume\right) \Rightarrow \left(\operatorname{MemLp}\left(b, 2, volume\right) \Rightarrow \operatorname{Integrable}\left((x: \mathbb{R} \mapsto \operatorname{a}\left(x\right) \cdot \operatorname{b}\left(x\right)), volume\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Asymptotics/CosineCutoffKernel.product_integrable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary complex functions a and b in Lebesgue L2, their pointwise product is Lebesgue integrable. The actual high-pass convolution uses this fact for each translated-reflected kernel row and every input.`D5/S3/Fourier/Asymptotics/CosineCutoffKernel/Highpass.actual_highpass_convolution`

## References

- Truth anchor: `D5/S3/Fourier/Asymptotics/CosineCutoffKernel.actual_cutoff_convolution`
- Truth anchor: `D5/S3/Fourier/Asymptotics/CosineCutoffKernel.actual_cutoff_inverse`
- Truth anchor: `D5/S3/Fourier/Asymptotics/CosineCutoffKernel.actual_cutoff_inverse`
- Truth anchor: `D5/S3/Fourier/Asymptotics/CosineCutoffKernel.actual_cutoff_real`
- Truth anchor: `D5/S3/Fourier/Asymptotics/CosineCutoffKernel.actual_weighted_cutoff`
- Truth anchor: `D5/S3/Fourier/Asymptotics/CosineCutoffKernel.kernel`
- Truth anchor: `D5/S3/Fourier/Asymptotics/CosineCutoffKernel.pair`
- Truth anchor: `D5/S3/Fourier/Asymptotics/CosineCutoffKernel.pair_eq`
- Truth anchor: `D5/S3/Fourier/Asymptotics/CosineCutoffKernel.product_integrable`
- Truth anchor: `D5/S3/Fourier/Asymptotics/CosineCutoffKernel.result`
- Truth anchor: `D5/S3/Fourier/Asymptotics/CosineCutoffKernel.symbol`
- Truth anchor: `D5/S3/Fourier/Asymptotics/CosineCutoffKernel/Highpass.actual_highpass_convolution`
- Dependency: [D5/S3/Fourier/Asymptotics/CosineCutoffKernel/GaussianWeight](CosineCutoffKernel/GaussianWeight.md)
- Dependency: [D5/S3/Quantum/Analysis/FourierWindowFiniteRank](../../Quantum/Analysis/FourierWindowFiniteRank.md)
