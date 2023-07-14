#include<stdio.h>
#include<stdlib.h>
#include<stdbool.h>
#include<math.h>

int mini(int a, int b){
    if(a>=b)return b;
    else return a;
}

float maxi(float a, float b){
    if(a>=b)return a;
    else return b;
}

//Differentiating Bits Structure
struct db{
    int r;
    int* b_bits;
};

//Masking Bits Structure
struct mb{
    int m;
    int* m_bits;
};

//Structure of Fusion Tree Node
struct FusionTree{
    int n;//number of keys
    int *key;//Pointer to array of keys
    bool leaf;// Whether node is leaf or not
    struct db* difbit;// Pointer to structure of differentiation bits
    struct mb* masbit;// Pointer to structure of masking bits
    int gap;
    int node_sketch;
    int mask_sketch;
    int mask_q;
    int mask_b;
    int mask_bm;
    struct FusionTree** next;// Pointer to array of pointers to next nodes
};

//Structure of root
struct root{
    struct FusionTree* r;// Pointer to root node
    int wor_len;
    float c;
    int w;
    int t;
};

//function to calculate the differentiating bits
struct db* DiffBits(struct root* rt,struct FusionTree* p){
    struct db* res;
    res=(struct db*)malloc(sizeof(struct db));
    int bits=0;
    for(int i=0;i<p->n;i++){
        for(int j=0;j<i;j++){
            int w=rt->w;
            while(((p->key[i] & 1 << w)==(p->key[j] & 1 << w)) && w>=0){
                w--;
            }
            if(w>=0)bits |= 1 << w;
        }
    }
    int i=0;
    res->r=0;
    while(i<rt->w){
        if((bits & (1 << i))> 0){
            res->r++;
        }
        i++;
    }
    res->b_bits=(int*)malloc(res->r*sizeof(int));
    int cnt=0;
    i=0;
    while(i<rt->w){
        if((bits & (1 << i))> 0){
            res->b_bits[cnt]=i;
            cnt++;
        }
        i++;
    }
    return res;
}

//function to calculate the masking bits and multiplication constant
struct mb* Const(struct root* rt,struct FusionTree* p){
    struct mb* res;
    res=(struct mb*)malloc(sizeof(struct mb));
    res->m_bits=(int*)malloc(p->difbit->r*sizeof(int));
    for(int i=0;i<p->difbit->r;i++)res->m_bits[i]=0;
    for(int t=0;t<p->difbit->r;t++){
        int mt=0;
        bool flag = true;
        while(flag == true){
            flag = false;
            for(int i=0;i<p->difbit->r;i++){
                if(flag == true)break;
                for(int j=0;j<p->difbit->r;j++){
                    if(flag==true)break;
                    for(int k=0;k<p->difbit->r;k++){
                        if(mt == (p->difbit->b_bits[i] - p->difbit->b_bits[j] + res->m_bits[k])){
                            flag = true;
                            break;
                        }
                    }
                }
            }
            if(flag == true)mt++;
        }
        res->m_bits[t] = mt;
    }
    res->m=0;
    for(int i=0;i<p->difbit->r;i++){
        res->m |= 1 << res->m_bits[i];
    }
    return res;
}

//to calculate mask of our node
int mask(int* temp,struct FusionTree* p){
    int res=0;
    for(int i=0;i<p->difbit->r;i++){
        res |= 1 << temp[i];
    }
    return res;
}

//function to calculate approximate sketch
int sketchap(struct root* rt,struct FusionTree* p, int x){
    int xx = x & p->mask_b;
    int res = xx * p->masbit->m;
    res = res & p->mask_bm;
    return res;
}
struct root *root;

struct FusionTree* allocateNode(int tn){
	struct FusionTree *temp;
	temp=(struct FusionTree*)malloc(sizeof(struct FusionTree));
	temp->key = (int*)malloc((2*tn)*sizeof(int));
	temp->leaf=1;
	temp->next = (struct FusionTree **)malloc((2*tn)*sizeof(struct FusionTree *));
	for(int i=0;i<2*tn;i++){
		temp->next[i]=NULL;
	}
	return temp;
	
}
//Creates a empty fusiontree
void fusionTreeCreate(){
	struct root* temp;
	temp=(struct root*)malloc(sizeof(struct root));
	temp->wor_len=64;
	temp->c=0.2;
	temp->t=maxi(pow(temp->wor_len,temp->c),2);
	temp->w=64;
	temp->r = allocateNode(temp->t);//Allocates space and initialize values for root node
	temp->r->n=0;
	root = temp;
} 
// Performs split child operation
void fusionTreeSplitChild(struct FusionTree *p,int i,int ta){
	struct FusionTree *z= allocateNode(ta);
	struct FusionTree *y= p->next[i];
	z->leaf=y->leaf;
	z->n=ta-1;
	for(int j=0;j<ta-1;j++){
		z->key[j]=y->key[j+ta];
	}
	if(y->leaf==0){
		for(int j=0;j<ta;j++){
			z->next[j]=y->next[j+ta];
		}
	}
	y->n=ta-1;
	for(int j=p->n;j>i;j--){
		p->next[j+1]=p->next[j];
	}
	p->next[i+1]=z;
	for(int j=p->n-1;j>i-1;j--){
		p->key[j+1]=p->key[j];
	}
	p->key[i]=y->key[ta-1];
	p->n++;
}
void fusionTreeInsertNonfull(struct FusionTree *p,int k, int ta){
	int i=p->n-1;
	if(p->leaf==1){
		while(i>=0 && k<p->key[i]){
			p->key[i+1]=p->key[i];
			i--;
		}
		p->key[i+1]=k;
		p->n++;
	}
	else{
		while(i>=0 && k<p->key[i]){
			i--;
		}
		i++;
		if(p->next[i]->n==2*ta-1){
			fusionTreeSplitChild(p,i,ta);
			if(k>p->key[i])
				i++;
		}
		fusionTreeInsertNonfull(p->next[i],k,ta);
	}
}
void fusionTreeInsert(int k,int ta){
	struct FusionTree *r = root->r;
	if(r->n == 2*ta-1){
		struct FusionTree *s = allocateNode(ta);
		s->leaf=0;
		s->n=0;
		s->next[0]=r;
		root->r=s;
		fusionTreeSplitChild(s,0,ta);
		fusionTreeInsertNonfull(s,k,ta);
	}
	else{
		fusionTreeInsertNonfull(r,k,ta);
	}
}

//function to initiate a node of our fusion tree
void initiatenode(struct root* rt,struct FusionTree* p){
    if(p->n!=0){
        p->difbit = DiffBits(rt,p);//calling function to calculate differentiating bits
        p->masbit = Const(rt,p);//calling function to calculate making bits
        p->mask_b = mask(p->masbit->m_bits,p);

        int * temp;//to store indices of imp bits
        temp=(int*)malloc(p->difbit->r*sizeof(int));

        for(int i=0;i<p->difbit->r;i++){
            temp[i]=(p->difbit->b_bits[i]+p->masbit->m_bits[i]);
        }
        p->mask_bm = mask(temp,p);

        int r3=pow(p->difbit->r,3);
        p->node_sketch=0;
        int sketch_len = r3+1;
        p->mask_sketch=0;
        p->mask_q = 0;
        for(int i=0;i<p->difbit->r;i++){
            int sketch = sketchap(rt,p,p->key[i]);
            temp[i]=1<<r3;
            temp[i] |= sketch;
            p->node_sketch <<= sketch_len;
            p->node_sketch |= temp[i];
            p->mask_q |= 1 << i*(sketch_len);
            p->mask_sketch |= (1 << (sketch_len - 1) << i*(sketch_len));
        }
    }
}
// This function use parallel comparision to compare keys in node
int paracomp(struct root *rt,struct FusionTree *p,int data){
	int sketch = sketchap(rt,p,data);
	int sketch_long = sketch*p->mask_q;
	int res = p->node_sketch-sketch_long;
	res = res&p->mask_sketch;
	int i=0;
	while((1<<i)<res){
		i++;
	}
	i++;
	int sketch_len = p->n*p->n*p->n+1;
	return (p->n-(i/sketch_len));
}

int successor(struct root *rt,struct FusionTree *p,int data){
    if(p==NULL)p=rt->r;

    if(p->n==0){
        if(p->leaf==1)return -1;
        else return successor(rt,p->next[0],data);
    }

    if(p->key[0]>=data){
        if(p->leaf==0){
            int res = successor(rt,p->next[0],data);
            if(res == -1)return p->key[0];
            else return mini(p->key[0],res);
        }
        else return p->key[0];
    }
    if(p->key[p->n-1]<data){
        if(p->leaf==true)return -1;
        else return successor(rt,p->next[p->n],data);
    }

    int pos = paracomp(rt,p,data);
if(pos>=p->n)pos-=p->n;
    
    if(pos==0){
        pos++;
    }

    int x = maxi(p->key[pos-1],p->key[pos]);

    int common_prefix = 0;
    int i=rt->w;
    while(i>0 && ((x&(1<<i))==(data&(1<<i)))){
        common_prefix |= x &(1<<i);
        i--;
    }
    if(i==-1)return x;

    int temp = common_prefix | (1<<i);

    pos = paracomp(rt,p,temp);
	
	if(pos>=p->n)pos-=p->n;

    if(p->leaf==1)return p->key[pos];
    else{
        int res = successor(rt,p->next[pos],data);
        if(res==-1)return p->key[pos];
        else return res;
    }
}


int predecessor(struct root *rt,struct FusionTree *p,int data){
    if(p==NULL)p=rt->r;

    if(p->n==0){
        if(p->leaf==0)return -1;
        else return predecessor(rt,p->next[0],data);
    }

    if(p->key[0]>data){
        if(p->leaf==0)return predecessor(rt,p->next[0],data);
        else return -1;
    }
    if(p->key[p->n-1]<=data){
        if(p->leaf==1)return p->key[p->n-1];
        else{
            int ret= predecessor(rt,p->next[p->n],data);
            return maxi(ret,p->key[p->n-1]);
        }
    }
    int pos = paracomp(rt,p,data);
if(pos>=p->n)pos-=p->n;
    if(pos==0){
        pos++;
    }

    int x = p->key[pos];

    int common_prefix = 0;
    int i=rt->w;
    while(i>=0 && ((x&(1<<i))==(data&(1<<i)))){
        common_prefix |= x &(1<<i);
        i--;
    }
    if(i==-1)return x;

    int temp = common_prefix | (1<<i);

    pos = paracomp(rt,p,temp);
if(pos>=p->n)pos-=p->n;
    if(pos==0){
        if(p->leaf==1)return p->key[pos];
        int res = predecessor(rt,p->next[1],data);
        if(res==-1)return p->key[pos];
        else return res;
    }

    if(p->leaf==1)return p->key[pos-1];
    else{
        int res = predecessor(rt,p->next[pos],data);
        if(res==-1)return p->key[pos-1];
        else return res;
    }

}

void initiate(struct FusionTree* ft){
    if(ft!=NULL){
		initiatenode(root,ft);
		if(ft->leaf == false){
			for(int i=0;i<(ft->n+1);i++){
				initiate(ft->next[i]);
			}
    	}
	}
}
	
void initiateTree(struct root* rt){
	initiate(root->r);
}
void fusionTreeInorderTransverse(struct FusionTree *p,int ta){
	if(p->leaf==1){
		for(int i=0;i<p->n;i++){
			printf("%d, ",p->key[i]);
		}
	}
	if(p->leaf==0){
		for(int i=0;i<p->n;i++){
			if(p->next[i]!=NULL){
				fusionTreeInorderTransverse(p->next[i],ta);
			}
			printf("%d, ",p->key[i]);
		}
		if(p->next[p->n]!=NULL){
			fusionTreeInorderTransverse(p->next[p->n],ta);
		}
	}
}
int main(){
    fusionTreeCreate();
    
    int lp=0;
    while(lp==0){
        char op;
				printf("options: I for insertion, S for sucessor, P for predecessor , E for exit ,T for traversal\n");
        scanf(" %c",&op);
        if(op=='I'){
            printf("Enter number of elements you wanted to enter:");
            int ne;
            scanf("%d",&ne);
            int *arr;
            arr=(int *)malloc(ne*sizeof(int));
            printf("Please enter the elements without any commas. for example to enter three numbers, enter them with a space between them like: 10 30 20\n");
            for(int i=0;i<ne;i++){
                scanf("%d",&arr[i]);
                fusionTreeInsert(arr[i],root->t);
            }
        }
        else if(op=='S'){
            struct root* rt=root;
            initiateTree(rt);
            int sr;
            printf("Enter an element to find sucessor of:\n");
            scanf("%d",&sr);
            int res = successor(root,root->r,sr);
            if(res == -1){
                printf("No successor\n");
            }
            else{
                printf("Sucessor is %d\n",res);
            }
        }
        else if(op=='P'){
            struct root* rt=root;
            initiateTree(rt);
            int sr;
            printf("Enter an element to find predecessor of:\n");
            scanf("%d",&sr);
            int res = predecessor(root,root->r,sr);
            if(res == -1){
                printf("No predecessor\n");
            }
            else{
                printf("Predecessor is %d\n",res);
            }
        }
        else if(op=='E'){
            lp++;
        }
	    else if(op=='T'){
				printf("Inorder traversal is: ");
				fusionTreeInorderTransverse(root->r,root->t);
				printf("\n");
			}
        else{
            printf("No valid command entered\n");
        }
    }

    return 0;
}
