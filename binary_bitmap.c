#include<stdlib.h>
#include<stdio.h>
#include<string.h>
#include<time.h>

////////////////////////////////////////////////////////////////////////////////////
struct ENTRY{
	unsigned int ip;
	unsigned char len;
	unsigned char port;
};
////////////////////////////////////////////////////////////////////////////////////
/*inline unsigned long long int rdtsc()
{
	unsigned long long int x;
	asm   volatile ("rdtsc" : "=A" (x));
	return x;
}*/
static __inline__ unsigned long long rdtsc(void)
{
  unsigned hi, lo;
  __asm__ __volatile__ ("rdtsc" : "=a"(lo), "=d"(hi));
  return ( (unsigned long long)lo)|( ((unsigned long long)hi)<<32 );
}
////////////////////////////////////////////////////////////////////////////////////
struct list{//structure of binary trie
	unsigned int port;
	struct list *left,*right,*parent;
    int count;
};
typedef struct list node;
typedef node *btrie;

struct list_bitmap{//structure of binary trie bitmap
	unsigned int inter_bit[7];
    unsigned int port[7];
    unsigned int exter_bit[8];
	struct list_bitmap *child[8];
};
typedef struct list_bitmap node_bitmap;
typedef node_bitmap *bitmap;
////////////////////////////////////////////////////////////////////////////////////
/*global variables*/
btrie root;
bitmap bitmap_root;
typedef struct list_element{
	unsigned int port;
	btrie root;
	struct ENTRY * list_table;
	int num;
} tentry;
tentry * segement_table;
int segement_array[65536];
unsigned int *query;
int num_entry=0;
int num_query=0;
struct ENTRY *table;
int N=0;//number of nodes
int max_segment_size=0;
unsigned long long int build_time=0;
unsigned long long int build_time_bitmap=0;
unsigned long long int total_bitmap=0;
unsigned long long int begin,end,total=0;
unsigned long long int *clock1;
int count=0;
int num_node=0;//total number of nodes in the binary trie
int num_node_bitmap=0;
int mem_access=0;
int layer0=0;
int count_sum[400000]={0};
////////////////////////////////////////////////////////////////////////////////////
void free_binary_trie(btrie root) {
    if (root == NULL) return;
    free_binary_trie(root->left);
    free_binary_trie(root->right);
    free(root);
}
////////////////////////////////////////////////////////////////////////////////////
bitmap create_bitmap(node *root);
// 計算指定節點的 inter_bit、exter_bit、port
void calculate_bits(node *current, bitmap bitmap_node) {

    // printf("%d\n",current->port);
    if (current != NULL) // root 有存在的話
    {
        if(current->port != 256)
            bitmap_node->inter_bit[0] = 1; // 設置對應的位元
        bitmap_node->port[0] = current->port;
    }
    // 檢查左子和右子是否存在
    if (current->left != NULL) // 左子
    {
        if(current->left->port != 256)
            bitmap_node->inter_bit[1] = 1; // 設置對應的位元
        bitmap_node->port[1] = current->left->port;
        if(current->left->left != NULL)//左子的左子存在
        {
            if(current->left->left->port != 256)
                bitmap_node->inter_bit[3] = 1;
            bitmap_node->port[3] = current->left->left->port;
            if(current->left->left->left != NULL && current->left->left->left->port != 256)
            {
                //左子的左子的左子存在
                bitmap_node->exter_bit[0] = 1;
            }
            if(current->left->left->right != NULL && current->left->left->right->port != 256)
            {
                //左子的左子的右子存在
                bitmap_node->exter_bit[1] = 1;
            }
        }
        if(current->left->right != NULL)//左子的右子存在
        {
            if(current->left->right->port != 256)
                bitmap_node->inter_bit[4] = 1;
            bitmap_node->port[4] = current->left->right->port;
            if(current->left->right->left != NULL && current->left->right->left->port != 256)
            {
                //左子的右子的左子存在
                bitmap_node->exter_bit[2] = 1;
            }
            if(current->left->right->right != NULL && current->left->right->right->port != 256)
            {
                //左子的右子的右子存在
               bitmap_node->exter_bit[3] = 1;
            }
        }
    }
    if (current->right != NULL) //右子
    {
        if(current->right->port != 256)
            bitmap_node->inter_bit[2] = 1; // 設置對應的位元
        bitmap_node->port[2] = current->right->port;
        if(current->right->left != NULL)//右子的左子存在
        {
            if(current->right->left->port != 256)
                bitmap_node->inter_bit[5] = 1;
            bitmap_node->port[5] = current->right->left->port;
            if(current->right->left->left != NULL && current->right->left->left->port != 256)
            {
                //右子的左子的左子存在
                bitmap_node->exter_bit[4] = 1;
            }
            if(current->right->left->right != NULL && current->right->left->right->port != 256)
            {
                //右子的左子的右子存在
                bitmap_node->exter_bit[5] = 1;
            }
        }
        if(current->right->right != NULL)//右子的右子存在
        {
            if(current->right->right->port != 256)
                bitmap_node->inter_bit[6] = 1;
            bitmap_node->port[6] = current->right->right->port;
            if(current->right->right->left != NULL && current->right->right->left->port != 256)
            {
                //右子的右子的左子存在
                bitmap_node->exter_bit[6] = 1;
            }
            if(current->right->right->right != NULL && current->right->right->right->port != 256)
            {
                //右子的右子的右子存在
                bitmap_node->exter_bit[7] = 1;
            }
        }
    }
}
// 遞歸構建 bitmap 二元樹的輔助函數
void build_bitmap_tree(node *current, bitmap bitmap_node) {
    if (current == NULL) {
        // printf("NULL\n");
        return ;
    }
    // 計算 inter_bit 和 exter_bit
    calculate_bits(current, bitmap_node);//build當前root對應的bitmap
    // printf("inter_bit: ");
    // for(int a=0;a<7;a++)
    //     printf("%d ",bitmap_node->inter_bit[a]);
    // printf("\n");
    // printf("port: ");
    // for(int a=0;a<7;a++)
    //     printf("%d ",bitmap_node->port[a]);
    // printf("\n");
    // 依序往下創建子bitmap(共8個)
    if(current->left != NULL)
    {
        if(current->left->left != NULL)
        {
            if (current->left->left->left != NULL ) //左左左
            {
                //先往下建立bitmap 0
                // printf("N:0\n");
                bitmap_node->child[0] = create_bitmap(current->left->left->left);
                for(int b=0; b<6; b++)//查得到的inter_bit是否有1 有則上層exter_bit設為1
                {
                    if(bitmap_node->child[0]->inter_bit[b] == 1)//有值就是1
                        bitmap_node->exter_bit[0] = 1;
                }
                if(bitmap_node->exter_bit[0] == 0)
                {
                    for(int b=0; b<7; b++)
                        if(bitmap_node->child[0]->exter_bit[b] == 1)//可能下層沒有東西但下下層有
                        {
                            bitmap_node->exter_bit[0] = 1;
                            break;
                        }
                }
                
            }
            if (current->left->left->right != NULL ) //左左右
            {
                //先往下建立bitmap 1
                // printf("N:1\n");
                bitmap_node->child[1] = create_bitmap(current->left->left->right);
                for(int b=0; b<6; b++)//查得到的inter_bit是否有1 有則上層exter_bit設為1
                {
                    if(bitmap_node->child[1]->inter_bit[b] == 1)//有值就是1
                        bitmap_node->exter_bit[1] = 1;
                }
                if(bitmap_node->exter_bit[1] == 0)
                {
                    for(int b=0; b<7; b++)
                        if(bitmap_node->child[1]->exter_bit[b] == 1)//可能下層沒有東西但下下層有
                        {
                            bitmap_node->exter_bit[1] = 1;
                            break;
                        }
                }
            }
        }
        if(current->left->right != NULL)
        {
            if (current->left->right->left != NULL ) //左右左
            {
                //先往下建立bitmap 2
                // printf("N:2\n");
                bitmap_node->child[2] = create_bitmap(current->left->right->left);
                for(int b=0; b<6; b++)//查得到的inter_bit是否有1 有則上層exter_bit設為1
                {
                    if(bitmap_node->child[2]->inter_bit[b] == 1)//有值就是1
                        bitmap_node->exter_bit[2] = 1;
                }
                if(bitmap_node->exter_bit[2] == 0)
                {
                    for(int b=0; b<7; b++)
                        if(bitmap_node->child[2]->exter_bit[b] == 1)//可能下層沒有東西但下下層有
                        {
                            bitmap_node->exter_bit[2] = 1;
                            break;
                        }
                }
            }
            if (current->left->right->right != NULL ) //左右右
            {
                //先往下建立bitmap 3
                // printf("N:3\n");
                bitmap_node->child[3] = create_bitmap(current->left->right->right);
                for(int b=0; b<6; b++)//查得到的inter_bit是否有1 有則上層exter_bit設為1
                {
                    if(bitmap_node->child[3]->inter_bit[b] == 1)//有值就是1
                        bitmap_node->exter_bit[3] = 1;
                }
                if(bitmap_node->exter_bit[3] == 0)
                {
                    for(int b=0; b<7; b++)
                        if(bitmap_node->child[3]->exter_bit[b] == 1)//可能下層沒有東西但下下層有
                        {
                            bitmap_node->exter_bit[3] = 1;
                            break;
                        }
                }
            }
        }
        
    }
    if(current->right != NULL)
    {
        if(current->right->left != NULL)
        {
            if (current->right->left->left != NULL ) //右左左
            {
                //先往下建立bitmap 4
                // printf("N:4\n");
                bitmap_node->child[4] = create_bitmap(current->right->left->left);
                for(int b=0; b<6; b++)//查得到的inter_bit是否有1 有則上層exter_bit設為1
                {
                    if(bitmap_node->child[4]->inter_bit[b] == 1)//有值就是1
                        bitmap_node->exter_bit[4] = 1;
                }
                if(bitmap_node->exter_bit[4] == 0)
                {
                    for(int b=0; b<7; b++)
                        if(bitmap_node->child[4]->exter_bit[b] == 1)//可能下層沒有東西但下下層有
                        {
                            bitmap_node->exter_bit[4] = 1;
                            break;
                        }
                }
            }
            if (current->right->left->right != NULL ) //右左右
            {
                //先往下建立bitmap 5
                // printf("N:5\n");
                bitmap_node->child[5] = create_bitmap(current->right->left->right);
                for(int b=0; b<6; b++)//查得到的inter_bit是否有1 有則上層exter_bit設為1
                {
                    if(bitmap_node->child[5]->inter_bit[b] == 1)//有值就是1
                        bitmap_node->exter_bit[5] = 1;
                }
                if(bitmap_node->exter_bit[5] == 0)
                {
                    for(int b=0; b<7; b++)
                        if(bitmap_node->child[5]->exter_bit[b] == 1)//可能下層沒有東西但下下層有
                        {
                            bitmap_node->exter_bit[5] = 1;
                            break;
                        }
                }
            }
        }
        if(current->right->right != NULL)
        {
            if (current->right->right->left != NULL ) //右右左
            {
                //先往下建立bitmap 6
                // printf("N:6\n");
                bitmap_node->child[6] = create_bitmap(current->right->right->left);
                for(int b=0; b<6; b++)//查得到的inter_bit是否有1 有則上層exter_bit設為1
                {
                    if(bitmap_node->child[6]->inter_bit[b] == 1)//有值就是1
                        bitmap_node->exter_bit[6] = 1;
                }
                if(bitmap_node->exter_bit[6] == 0)
                {
                    for(int b=0; b<7; b++)
                        if(bitmap_node->child[6]->exter_bit[b] == 1)//可能下層沒有東西但下下層有
                        {
                            bitmap_node->exter_bit[6] = 1;
                            break;
                        }
                }
            }
            if (current->right->right->right != NULL ) //右右右
            {
                //先往下建立bitmap 7
                // printf("N:7\n");
                bitmap_node->child[7] = create_bitmap(current->right->right->right);
                for(int b=0; b<6; b++)//查得到的inter_bit是否有1 有則上層exter_bit設為1
                {
                    if(bitmap_node->child[7]->inter_bit[b] == 1)//有值就是1
                    {
                        bitmap_node->exter_bit[7] = 1;
                        break;
                    }
                }
                if(bitmap_node->exter_bit[7] == 0)
                {
                    for(int b=0; b<7; b++)
                        if(bitmap_node->child[7]->exter_bit[b] == 1)//可能下層沒有東西但下下層有
                        {
                            bitmap_node->exter_bit[7] = 1;
                            break;
                        }
                }
            }
        }  
    }
    // printf("exter_bit: ");
    // for(int a=0; a<8; a++)
    //     printf("%d ",bitmap_node->exter_bit[a]);
    // printf("\n");

}
// 創建 bitmap 二元樹
bitmap create_bitmap(node *root) {
    // 創建根節點
    num_node_bitmap++;
    bitmap bitmap_root = (bitmap)malloc(sizeof(node_bitmap));
    for (int i = 0; i < 7; i++) {
        bitmap_root->inter_bit[i] = 0;
        bitmap_root->port[i] = 256; // 預設端口為 256
    }
    for (int i = 0; i < 8; i++) {
        bitmap_root->exter_bit[i] = 0;
        bitmap_root->child[i] = NULL;
    }

    // 遞歸構建 bitmap 二元樹
    build_bitmap_tree(root, bitmap_root);

    return bitmap_root;
}


////////////////////////////////////////////////////////////////////////////////////
btrie create_node(){
	btrie temp;
	num_node++;
	temp=(btrie)malloc(sizeof(node));
	temp->right=NULL;
	temp->left=NULL;
    temp->parent=root;
    temp->count=0;
	temp->port=256;//default port
	return temp;
}
////////////////////////////////////////////////////////////////////////////////////
void add_node(unsigned int ip,unsigned char len,unsigned char nexthop){  //16-bits segment
	btrie ptr=root;
    btrie temp=root;
	int i = 0;
	len = len - 16;
	for(i=0;i<len;i++){
        if(ptr->port != 256) temp = ptr;
		if(ip&(1<<(15-i))){
			if(ptr->right==NULL)
				ptr->right=create_node(); // Create Node
			ptr=ptr->right;
            ptr->parent = temp;
			if((i==len-1)&&(ptr->port==256)){
				ptr->port=nexthop;
                ptr->parent->count = ptr->parent->count+1;
            }
		}
		else{
			if(ptr->left==NULL)
				ptr->left=create_node();
			ptr=ptr->left;
            ptr->parent = temp;
			if((i==len-1)&&(ptr->port==256)){
				ptr->port=nexthop;
                ptr->parent->count = ptr->parent->count+1;
            }
		}
        // printf("%d\n",ptr->port);
	}
    // printf("%d\n",ptr->port);
}
// void add_node(unsigned int ip,unsigned char len,unsigned char nexthop){ // non-segment
// 	btrie ptr=root;
// 	int i;
// 	for(i=0;i<len;i++){
// 		if(ip&(1<<(31-i))){
// 			if(ptr->right==NULL)
// 				ptr->right=create_node(); // Create Node
// 			ptr=ptr->right;
// 			if((i==len-1)&&(ptr->port==256)){
// 			//	count++;
// 				ptr->port=nexthop;
// 			}
				
// 		}
// 		else{
// 			if(ptr->left==NULL)
// 				ptr->left=create_node();
// 			ptr=ptr->left;
// 			if((i==len-1)&&(ptr->port==256)){
// 			//		count++;
// 				ptr->port=nexthop;
// 			}
				
// 		}
// 	}
// }
////////////////////////////////////////////////////////////////////////////////////
unsigned long long int insert_time[65536]={0};
void build_segment_create( int pos ){
	int i;
	root=create_node();
	begin=rdtsc();
	for(i=0;i<segement_table[pos].num;i++){
		add_node(segement_table[pos].list_table[i].ip,segement_table[pos].list_table[i].len,segement_table[pos].list_table[i].port);
	}
	end=rdtsc();
	insert_time[pos]=end-begin;
	segement_table[pos].root = root;
}
////////////////////////////////////////////////////////////////////////////////////
void inition(){
	segement_table= (tentry*)malloc( 65536* sizeof(tentry) );
	int i;
	for( i = 0; i < 65536; i++ ){
		segement_table[i].num = 0;
		segement_table[i].port = 256;
		segement_table[i].root = NULL;
		segement_table[i].list_table = (struct ENTRY *)malloc( (max_segment_size+1) * sizeof(struct ENTRY));
	}
}
void build_segement_table(){
	for(int i=0;i<65536;i++)
		segement_array[i]=256;
	int num[65536]={0};
	unsigned int ip = 0;
	unsigned int ip_max = 0;
	int prefix_dis[16] = {0};
	for(int i=0;i<num_entry;i++){
		unsigned int temp_min = 0,temp_max=0;
		if(table[i].len > 16){
			for(int k = 0; k < 16; k++ ) {
				if( table[i].ip & (1<< (31-k)) ){
					temp_min += 1 << (15-k);
				}
			}
			num[temp_min]++;
		}
	}
	max_segment_size = num[0];
	int max_index;
	for(int i=1;i<65536;i++){
		if(num[i] > max_segment_size){
			max_segment_size = num[i];
			max_index=i;
		}
	}
	printf("max_segment_size =%d, index = %d\n",max_segment_size,max_index);
	inition();
	for(int i = 0; i < num_entry; i++ ){
		if( table[i].len > 16 ){ 
			ip = table[i].ip>>16;
			segement_table[ip].list_table[segement_table[ip].num].len = table[i].len;
			segement_table[ip].list_table[segement_table[ip].num].ip = table[i].ip;
			segement_table[ip].num++;
		}
		else if(table[i].len == 16){
			ip = table[i].ip>>16;
			segement_array[ip]=1;
		}
		else{ 
			ip = table[i].ip>>16;
			ip_max = ip +(1<<(16-table[i].len))-1;
			for(int j=ip;j<=ip_max;j++){
				segement_array[j]=1;
			}
		}


	}
	int non_empty_entry = 0;
	int empty_entry = 0;

	for(int i = 1; i < 65536; i++ ){
		if ( segement_table[i].num == 0 )
			empty_entry++;
		else{
			non_empty_entry++;
			build_segment_create(i);
		}
	}
	printf("empty_segment =%d , non_empty_segment =%d\n",empty_entry,non_empty_entry);

}
///////////////////////////////////////////////////////////////////////////////////////
void read_table(char *str,unsigned int *ip,int *len,unsigned int *nexthop){
	char tok[]="./";
	char buf[100],*str1;
	unsigned int n[4];
    //ip=213.108.208.0/21
    //n[0]=213、n[1]=108、n[2]=208、n[3]=0、
	sprintf(buf,"%s\0",strtok(str,tok));
	n[0]=atoi(buf);
	sprintf(buf,"%s\0",strtok(NULL,tok));
	n[1]=atoi(buf);
	sprintf(buf,"%s\0",strtok(NULL,tok));
	n[2]=atoi(buf);
	sprintf(buf,"%s\0",strtok(NULL,tok));
	n[3]=atoi(buf);
	*nexthop=n[2];
	str1=(char *)strtok(NULL,tok);
	if(str1!=NULL){
		sprintf(buf,"%s\0",str1);
		*len=atoi(buf);
	}
	else{
		if(n[1]==0&&n[2]==0&&n[3]==0)
			*len=8;
		else
			if(n[2]==0&&n[3]==0)
				*len=16;
			else
				if(n[3]==0)
					*len=24;
	}
	*ip=n[0];
	*ip<<=8;
	*ip+=n[1];
	*ip<<=8;
	*ip+=n[2];
	*ip<<=8;
	*ip+=n[3];
    // printf("%d\t%d\t%d\t%d\n",n[0],n[1],n[2],n[3]);
    // printf("%u\n",*ip);
}
////////////////////////////////////////////////////////////////////////////////////
int find,success=0,fail=0;
void search(unsigned int ip,btrie root){
	int j;
	find=0;
	btrie current=root,temp=NULL;
	for(j=31;j>=(-1);j--){
		if(current==NULL)
			break;
		if(current->port!=256){
			temp=current;
			find=1;
		}
		if(ip&(1<<j)){
			current=current->right;
		}
		else{
			current=current->left; 
		}
	}
	
}
void search_segment(unsigned int ip){
	unsigned int ip_temp;
	int j;
	find=0;
	ip_temp = ip>>16;
	btrie current=segement_table[ip_temp].root,temp=NULL;
	mem_access++;
	for(j=15;j>=(-1);j--){
		if(current==NULL)
			break;
		if(current->port!=256){
			temp=current;
			find=1;
            // printf("%d\n",current->port); //只有0跟256
		}
		if(ip&(1<<j)){
			current=current->right;
		}
		else{
			current=current->left; 
		}
		mem_access++;
        
	}
	if(find)
		success++;
	else{
		if(segement_array[ip_temp]!=256)
			success++;
		else
			fail++;
	}

}
////////////////////////////////////////////////////////////////////////////////////
int less16=0,equal16=0;
void set_table(char *file_name){
	FILE *fp;
	int len;
	char string[100];
	unsigned int ip,nexthop;
	fp=fopen(file_name,"r");
	while(fgets(string,50,fp)!=NULL){
		read_table(string,&ip,&len,&nexthop);
		num_entry++;
	}
	rewind(fp);
	table=(struct ENTRY *)malloc(num_entry*sizeof(struct ENTRY));
	num_entry=0;
	while(fgets(string,50,fp)!=NULL){
		read_table(string,&ip,&len,&nexthop);
		if(len<16)
			less16++;
		else if(len==16)
			equal16++;
		table[num_entry].ip=ip;
		table[num_entry].port=nexthop;
		table[num_entry++].len=len;
	}
}
////////////////////////////////////////////////////////////////////////////////////
void set_query(char *file_name){
	FILE *fp;
	int len;
	char string[100];
	unsigned int ip,nexthop;
	fp=fopen(file_name,"r");
	while(fgets(string,50,fp)!=NULL){
		read_table(string,&ip,&len,&nexthop);
		num_query++;
	}
	rewind(fp);
	query=(unsigned int *)malloc(num_query*sizeof(unsigned int));
	clock1=(unsigned long long int *)malloc(num_query*sizeof(unsigned long long int));
	num_query=0;
	while(fgets(string,50,fp)!=NULL){
		read_table(string,&ip,&len,&nexthop);
		query[num_query]=ip;
		clock1[num_query++]=10000000;
	}
}
////////////////////////////////////////////////////////////////////////////////////
void create(){
	int i;
	root=create_node();
	begin=rdtsc();
	for(i=0;i<num_entry;i++)
		add_node(table[i].ip,table[i].len,table[i].port);
	end=rdtsc();
	build_time=end-begin;
}
////////////////////////////////////////////////////////////////////////////////////
void count_node(btrie r){ //­pºânexthopªºnode­Ó¼Æ 
//	printf("aa\n");
	if(r==NULL) return;
	count_node(r->left);
	//count_node(r->right);
	if(r->port!=256) count++;
    if(r->count!=0 && r->port!=256) for(int i=1; i<400000; i++) {if(r->count == i) count_sum[i]++;}
    if(r->count==0 && r->port!=256) layer0++;
	count_node(r->right);
}
////////////////////////////////////////////////////////////////////////////////////
void CountClock()
{
	unsigned int i;
	unsigned int* NumCntClock = (unsigned int* )malloc(50 * sizeof(unsigned int ));
	for(i = 0; i < 50; i++) NumCntClock[i] = 0;
	unsigned long long MinClock = 10000000, MaxClock = 0;
	for(i = 0; i < num_query; i++)
	{
		if(clock1[i] > MaxClock) MaxClock = clock1[i];
		if(clock1[i] < MinClock) MinClock = clock1[i];
		if(clock1[i] / 100 < 50) NumCntClock[clock1[i] / 100]++;
		else NumCntClock[49]++;
	}
	printf("(MaxClock, MinClock) = (%5llu, %5llu)\n", MaxClock, MinClock);
	FILE *fp;
	fp=fopen("cycle.txt","w");
	for(i = 0; i < 50; i++)
	{	
		fprintf(fp,"%d\n",NumCntClock[i]);
		printf("%d\n", NumCntClock[i]);
	}
	fclose(fp);
	return;
}
//shuffle有點問題 找不到
// void shuffle(int *array, size_t n){
//     //亂數前置
//     srand(time(NULL));
//     if (n > 1){
//         size_t i;
//         for (i = 0; i<n; i++){
//             size_t j = rand()/(RAND_MAX/(n));
//             unsigned int t = array[j];
//             array[j] = array[i];
//             array[i] = t;
//         }
//     }
// }
////////////////////////////////////////////////////////////////////////////////////
void print_trie(btrie root)
{
    if(root != NULL)
    {
        printf("%d\t",root->port);
        printf(" L:");
        print_trie(root->left);
        printf(" R:");
        print_trie(root->right);
    } 
}
int find_bitmap,success_bitmap=0,fail_bitmap=0,bit_access=0;
void search_bitmap(unsigned int ip)
{
    bitmap temp_bitmap = bitmap_root;
    int c;
    unsigned int temp_port;
    find_bitmap=0;
    unsigned int next_hop = (ip >> 8) & 0xFF;//移過去8位元 且 and 8個1 就得到port
    // printf("%d\n",next_hop);
    //先檢查inter(3bit+3bit)
    for(c=2;c>0;c--)
    {
        unsigned int next_0 = (next_hop >> (3 * c) + 1) & 0x01;//c=2,7 c=1,4
        unsigned int next_1 = (next_hop >> 3 * c) & 0x01;
        unsigned int next_2 = (next_hop >> (3 * c) - 1) & 0x01;
        unsigned int next_02 = (next_hop >> 5) & 0x07;
        // printf("%d\t%d\t%d\n",next_0,next_1,next_2);
        if(temp_bitmap->inter_bit[1+next_0] == 1)//第一層有找到值
        {
            find_bitmap=1;
            temp_port=temp_bitmap->port[1+next_0];
            bit_access++;
        }
        if(temp_bitmap->inter_bit[3+next_1+(next_0*2)] == 1)//第二層有找到值
        {
            find_bitmap=1;
            temp_port=temp_bitmap->port[3+next_1+(next_0*2)];
            bit_access++;
        }
        if(temp_bitmap->exter_bit[next_02] == 1)//exter 有值
        {
            if(next_0 == 0 && next_1 == 0 && next_2 == 0)//000
            {
                temp_bitmap=temp_bitmap->child[0];
            }
            else if(next_0 == 0 && next_1 == 0 && next_2 == 1)//001
            {
                temp_bitmap=temp_bitmap->child[1];
            }
            else if(next_0 == 0 && next_1 == 1 && next_2 == 0)//010
            {
                temp_bitmap=temp_bitmap->child[2];
            }
            else if(next_0 == 0 && next_1 == 1 && next_2 == 1)//011
            {
                temp_bitmap=temp_bitmap->child[3];
            }
            else if(next_0 == 1 && next_1 == 0 && next_2 == 0)//100
            {
                temp_bitmap=temp_bitmap->child[4];
            }
            else if(next_0 == 1 && next_1 == 0 && next_2 == 1)//101
            {
                temp_bitmap=temp_bitmap->child[5];
            }
            else if(next_0 == 1 && next_1 == 1 && next_2 == 0)//110
            {
                temp_bitmap=temp_bitmap->child[6];
            }
            else if(next_0 == 1 && next_1 == 1 && next_2 == 1)//111
            {
                temp_bitmap=temp_bitmap->child[7];
            }
        }
        else if(temp_bitmap->exter_bit[next_02] == 0)//exter 沒東西
            break;
        }
    //做最後一次的2bit 
    if(c == 0)
    {
        unsigned int next_0 = (next_hop >> 1) & 0x01;
        unsigned int next_1 = (next_hop >> 0) & 0x01;
        // printf("%d\t%d\n",next_0,next_1);
        if(temp_bitmap->inter_bit[1+next_0] == 1)//第一層有找到值
        {
            find_bitmap=1;
            temp_port=temp_bitmap->port[1+next_0];
            bit_access++;
        }
        if(temp_bitmap->inter_bit[3+next_1+(next_0*2)] == 1)//第二層有找到值
        {
            find_bitmap=1;
            temp_port=temp_bitmap->port[3+next_1+(next_0*2)];
            bit_access++;
        }
    }

    if(find_bitmap)
        success_bitmap++;
    else
        fail_bitmap++;
    // printf("s:%d\tf:%d\n",success_bitmap,fail_bitmap);

}
int main(int argc,char *argv[]){
	
	unsigned long long int total_insert=0;
	int i,j,sum=0;
	set_query(argv[2]);
	set_table(argv[1]);
	printf("# of prefix = %d\n",num_entry);
	printf("# of prefix is len < 16 = %d\n",less16);
	printf("# of prefix is len = 16 = %d\n",equal16);
	create();
	printf("avg build time=%llu\n",build_time/num_query);
	build_segement_table();
	//btrie ptr=root;
	count_node(root);
	for(int k=0; k<400000; k++)
	{	
		if(count_sum[k]!=0)
			printf("%d subnode = %d\n", k, count_sum[k]);
	}
	for(int k=0; k<400000; k++)
		sum+=count_sum[k];
	printf("number of layer0: %d\n",layer0);
	printf("number of sum: %d\n",sum);
	for(int k=1;k<65536;k++){
		total_insert+=insert_time[k];
	}
	printf("1");
	// shuffle(query, num_query);
	printf("2\n");
	printf("Avg. Insert: %llu\n",total_insert/num_entry);//bulid time
	printf("number of nodes: %d\n",num_node);
	printf("Total memory requirement: %d KB\n",((num_node*12)/1024));
	////////////////////////////////////////////////////////////////////////////
	FILE *fp;
	fp = fopen("cycles_record.txt", "w"); // 以附加模式打開文件
	for(j=0;j<100;j++){
		printf("The %d searching\n",j+1);
		for(i=0;i<num_query;i++)
        {
			begin=rdtsc();
			//search(query[i],root);
			search_segment(query[i]);
			end=rdtsc();
			if(clock1[i]>(end-begin))
				clock1[i]=(end-begin);
			
			if (fp == NULL) {
				printf("Error opening file!\n");
			}
			fprintf(fp, "%llu\n", clock1[i]); // search每個IP的CPU周期數
		}
	}
	fclose(fp); // 關閉文件
	printf("mem_access =%d, Avg mem_access = %f\n", mem_access,(float)mem_access/(float)num_query );
	total=0;
	for(j=0;j<num_query;j++)
		total+=clock1[j];
	printf("Avg. Search: %llu\n",total/num_query);
	CountClock();
    // print_trie(root);
    printf("start build\n");
    begin=rdtsc();
    bitmap_root = create_bitmap(root);
    end=rdtsc();
    build_time_bitmap = end - begin ;
    printf("finish build\n");
    //search bitmap
    unsigned long long int *clock_bitmap=(unsigned long long int *)malloc(num_query*sizeof(unsigned long long int));
    for(int a=0; a<num_query; a++)
        clock_bitmap[a]=10000000;
    FILE *fp_bitmap;
	fp_bitmap = fopen("cycles_record_bitmap.txt", "w"); // 以附加模式打開文件
	for(j=0;j<100;j++){
		printf("The %d searching bitmap\n",j+1);
		for(i=0;i<num_query;i++)
        {
			begin=rdtsc();
			search_bitmap(query[i]);
			end=rdtsc();
			if(clock_bitmap[i]>(end-begin))
				clock_bitmap[i]=(end-begin);
			
			if (fp_bitmap == NULL) {
				printf("Error opening file!\n");
			}
			fprintf(fp_bitmap, "%llu\n", clock_bitmap[i]); // search每個IP的CPU周期數
		}
	}
    for(j=0;j<num_query;j++)
		total_bitmap+=clock_bitmap[j];
    // printf("meow:%d\t%d\n",sizeof(struct list),sizeof(struct list_bitmap));
    printf("Time of build bitmap : %llu\n", build_time_bitmap/num_node_bitmap);
	printf("Avg. bitmap Search: %llu\n",total_bitmap/num_query);
    printf("Number of nodes:%d\n",num_node_bitmap);
    printf("Total memory requirement: %d KB\n",((num_node_bitmap*120)/1024));
    printf("bitmap: s= %d\tf= %d\n",success_bitmap,fail_bitmap);
    printf("binary: s= %d\tf= %d\n",success,fail);
	fclose(fp_bitmap); // 關閉文件

	free(query);
	free(clock1);
	free(table);
	for(int i = 0; i < 65536; i++) {
		free(segement_table[i].list_table);
	}
	free(segement_table);
	free_binary_trie(root);
	return 0;
}
