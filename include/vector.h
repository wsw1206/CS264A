#ifndef VECTOR_H_
#define VECTOR_H_

typedef unsigned long c2dSize;

typedef struct {
	void** data;
	c2dSize capacity;
	c2dSize size;
} vector;

void vector_init(vector*);
c2dSize vector_size(const vector*);
void vector_push(vector*, void*);
void vector_pop(vector*);
void* vector_get(const vector*, c2dSize);
void* vector_top(const vector*);
void vector_set(vector*, c2dSize, void*);
void vector_erase(vector*, c2dSize);
void vector_free(vector*);
void** vector_toarr(const vector*);

#endif
